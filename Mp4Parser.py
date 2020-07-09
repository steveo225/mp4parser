# system imports
import json
import os
import sys
import xml.etree.ElementTree as ET

from hashlib import md5
from io      import BytesIO
from math    import ceil
from PIL     import Image
from struct  import unpack
from time    import time, sleep

# gui imports
from PyQt5.QtCore    import Qt, QByteArray, QThread, pyqtSignal
from PyQt5.QtGui     import QCursor, QIcon, QPixmap
from PyQt5.QtWidgets import QApplication, QDialog, QFileDialog, QHBoxLayout, QLabel, QMessageBox, \
                            QProgressBar, QPushButton, QSizePolicy, QStyle, QVBoxLayout, QWidget
try: from PyQt5 import QtWinExtras
except: pass

#--------------------------------------------------------------------------------------------------
# @brief Class to read and parse MP4/M4A meta data tags.
class Mp4Parser(dict):
    #----------------------------------------------------------------------------------------------
    # @brief List of tags that represent containers with additional key/values.
    CONTAINERS = [b'dinf', b'edts', b'ilst', b'gmhd', b'mdia', b'meta', b'minf', b'moov', b'stbl',
                  b'trak', b'tref', b'udta']

    #----------------------------------------------------------------------------------------------
    # @brief List of tags that can be ignored (most represent vidoe parsing information).
    # co64: 
    # ctts: composition offset atom; sample-by-sample mapping of the decode-to-presentation time
    # dref: data reference atom; data handler instructions for how to access the media's data
    # elst: edit list atoms; map from a time in a movie to a time in a media
    # free: free space
    # hdlr: handler reference atoms; media handler component for interpreting the media's data
    # mdat: media data; raw media chunks
    # sdtp: sample dependency flags atom; 1 byte/sample as a bit field that describes dependency
    # stco: chunk offset atoms; identify the location of each chunk of data
    # stsc: sample-to-chunk atoms; contain a table that maps samples to chunks
    # stsd: sample description atoms; contain a table of sample descriptions
    # stss: sync sample atom; identifies the key frames
    # stts: time-to-sample atoms; mapping from a time in a media to the corresponding data sample
    # stsz: sample size atoms; specify the size of each sample
    IGNORE = [b'co64', b'ctts', b'dref', b'elst', b'free', b'hdlr', b'mdat', b'sdtp', b'stco',
              b'stsc', b'stsd', b'stss', b'stts', b'stsz']

    #----------------------------------------------------------------------------------------------
    # @brief Mapping of tag to human readable title.
    TITLES = { b'\xa9alb':  'Album',
               b'\xa9ART':  'Cast',
               b'\xa9nam':  'Title',
               b'\xa9day':  'Released',
               b'\xa9gen':  'Genre',
               b'\xa9cmt':  'Comment',
               b'\xa9wrt':  'Writer',
               b'\xa9too':  'Tool',
               b'cnID':     'Catalog ID',
               b'covr':     'Cover',
               b'desc':     'Description',
               b'ftyp':     'File type compatibility',
               b'gmin':     'Base media information',
               b'hdvd':     'High definition',
               b'iTunEXTC': 'iTunes content rating',
               b'iTunMOVI': 'iTunes movie information',
               b'ldes':     'Description',
               b'mdhd':     'Media header',
               b'mvhd':     'Movie header',
               b'sdes':     'Show description',
               b'smhd':     'Sound media informtion',
               b'stik':     'Media type',
               b'tkhd':     'Track header',
               b'tref':     'Track reference',
               b'trkn':     'Track number',
               b'tven':     'Episode title',
               b'tvnn':     'TV station',
               b'tves':     'TV episode',
               b'tvsh':     'TV show',
               b'tvsn':     'TV season',
               b'vmhd':     'Video info' }

    #----------------------------------------------------------------------------------------------
    # @brief Construct a dictionary by reading the atom tags.
    # @param filename - file path and name to open and parse
    def __init__(self, filename=None):
        super(dict, self).__init__()
        if filename is None: return

        with open(filename, 'rb') as fd:
            fd.seek(0, 2) # go to the end of the file for the size
            for type, data in self._parse(fd, 0, fd.tell()):
                self._save(type, data)
            #
        #
    # end constructor

    #----------------------------------------------------------------------------------------------
    # @brief Parse a range of data for atoms within the file.
    # @param start - starting offset to look for tags
    # @param end - ending offset not to exceed
    # @yields a tuple(tag, data)
    def _parse(self, fd, begin, end):
        offset = begin
        try:
            while offset < end:
                fd.seek(offset)
                size = unpack('!I', fd.read(4))[0]
                tag = fd.read(4)

                if size == 1: # if size is too big for a uint32
                    size = unpack('!Q', fd.read(8))[0] - 8
                    offset += 8
                #

                if tag in Mp4Parser.CONTAINERS:
                    skip = 12 if tag == b'meta' else 8
                    for atom in self._parse(fd, offset+skip, offset+size):
                        yield atom
                    #
                #
                elif not tag in Mp4Parser.IGNORE:
                    data = fd.read(size-8)
                    yield tag, data
                #
                offset += size
            #
        #
        except:
            pos = fd.tell()
            fd.seek(0, os.SEEK_END)
            fsize = fd.tell()

            print(f'File size: {fsize}')
            print(f'File position: {pos}')
            print(f'Range: {begin} -> {end}')
            print(f'Tag: {tag}')
            print(f'Offset: {offset}')
            print(f'Size: {size}')
        #
    # end _parse

    #----------------------------------------------------------------------------------------------
    # @brief Save an atom from the raw key/value pair.
    # @param tag - name of the parsed tag
    # @param value - value of the parsed tag
    def _save(self, tag, value):
        # special case tag to save extra meta data (converts to another tag)
        if tag == b'----': 
            offset = 0
            result = {}
            while offset < len(value):
                size = unpack("!i", value[offset:offset+4])[0]
                type = value[offset+4:offset+8]
                result[type] = value[offset+12:offset+size]
                offset += size
            #

            # currently known keys are: mean, name, and data
            # 'mean' is always 'com.apple.iTunes'
            # 'name' is always 'iTunMOVI' or 'iTunEXTC'
            tag   = result[b'name']
            value = result[b'data']
        #

        # determine a key for the dictionary
        key = Mp4Parser.TITLES[tag] if tag in Mp4Parser.TITLES else tag

        # apply converters if necessary
        # Note: fixed32 is really int16 whole number and int16 decimal
        #       fixed16 is similar with int8
        #       a parsing cheat exists: read a fixed32 as int32 and divide by 65536
        # Note: many fields are sub fields that have a 4 bytes subheader (1: version, 3: flags)
        #       the remaining have a 16 byte subheader
        # See: https://developer.apple.com/library/archive/documentation/QuickTime/QTFF/QTFFChap2/qtff2.html
        # See: https://developer.apple.com/library/archive/documentation/QuickTime/QTFF/QTFFChap4/qtff4.html
        if tag in [b'\xa9ART', b'\xa9gen']:
            # convert a comma delimited list to Python list
            value = value[16:].decode('utf-8').split(', ')
        #
        elif tag in [b'cnID', b'tves', b'tvsn']:
            # convert from binary integer to Python integer
            value = int.from_bytes(value[16:], byteorder='big')
        #
        elif tag == b'hdvd':
            # convert from byte array to bool
            value = False # actually determine from width, it is more reliable
        #
        elif tag == b'iTunEXTC':
            # 1: version
            # 3: flags
            # N (string): <standard>|<rating>|<score>|<reason> (e.g. mpaa|PG-13|300|)
            values = value[4:].decode('utf-8').split('|')
            value = { 'Rating': values[1] } # only keep the rating portion for now
        #
        elif tag == b'iTunMOVI':
            # parse an embedded XML document into a dictionary
            results = {}
            root = ET.fromstring(value[4:].decode('utf-8'))
            for node in root.find('dict'):
                if node.tag == 'key':
                    key = node.text[0].upper() + node.text[1:]
                #
                elif key and node.tag == 'array':
                    results[key] = [dict.find('string').text for dict in node.findall('dict')]
                    key = ''
                #
                elif key and node.tag == 'string':
                    results[key] = node.text
                    key = ''
                #
            #
            value = results
        #
        elif tag == b'ftyp':
            # 4 (uint32)> major brand
            # 4 (uint32)> minor version
            # N (uint32 list)> compatible brands
            # Note: major brand must be set to or compatible brands must include b'qt  ' to be
            #       considered a compatible QuickTime media file
            value = False # ingore for now
        #
        elif tag == b'gmin':
            # 1> version
            # 3> flags
            # 2 (uint16)> graphics mode
            # 6 (3 x uint16)> opcolor (r, g, b)
            # 2 (uint16)> sound balance
            # 2> reserved
            value = False # ignore for now
        #
        elif tag == b'mdhd': # characteristics of the media
            #    1> version
            #    3> flags
            # 0: 4 (uint32)> atom creation time (seconds since 1-1-1904)
            # 1: 4 (uint32)> atom modification time (seconds since 1-1-1904)
            # 2: 4 (uint32)> time scale (number of time units per second)
            # 3: 4 (uint32)> media duration
            # 4: 2 (uint16)> language code
            # 5: 2 (uint16)> media playback quality
            values = unpack('>x3x4I2H', value)
            value = False # ignore for now
        #
        elif tag == b'mvhd': # characteristics of the entire media
            #    1> version
            #    3> flags
            # 0: 4 (uint32)> atom creation time (seconds since 1-1-1904)
            # 1: 4 (uint32)> atom modification time (seconds since 1-1-1904)
            # 2: 4 (uint32)> time scale (number of time units per second)
            # 3: 4 (uint32)> duration
            # 4: 4 (fixed32)> preferred rate at which to play this movie; 1.0 indicates normal rate
            # 5: 2 (fixed16)> preferred volume; 1.0 indicates full volume
            #    10> reserved
            #    36 (9 x fixed32)> mapping of points from one coordinate space into another
            #    4> preview time start
            #    4> preview duration
            #    4> movie poster time
            #    4> selection start time
            #    4> selection duration
            #    4> current time position within the movie
            #    4 (uint32)> next track ID
            values = unpack('>x3x4IIH74x', value)
            value = { 'Duration': values[3] / values[2] }
        #
        elif tag == b'smhd':
            # 1> version
            # 3> flags
            # 2 (uint16)> sound balance
            # 2> reserved
            value = False
        #
        elif tag == b'stik':
            # convert from binary integer to enumeration
            value = int.from_bytes(value[17:], byteorder='little', signed=False)
            if   value == 0:  value = 'Movie'
            elif value == 1:  value = 'Music'
            elif value == 2:  value = 'Audiobook'
            elif value == 6:  value = 'Music video'
            elif value == 9:  value = 'Movie'
            elif value == 10: value = 'TV show'
            elif value == 11: value = 'Booklet'
            elif value == 14: value = 'Ringtone'
            elif value == 21: value = 'Podcast'
            elif value == 23: value = 'iTunes U'
            else:             value = f'Unknown #{value}'
        #
        elif tag == b'tkhd': # characteristics of a single track
            #    1> version
            #    3> flags
            # 0: 4 (uint32)> atom creation time (seconds since 1-1-1904)
            # 1: 4 (uint32)> atom modification time (seconds since 1-1-1904)
            # 2: 4 (uint32)> track ID
            #    4> reserved
            # 3: 4 (uint32)> duration
            #    8> reserved
            # 4: 2 (uint16)> layer (lower is higher z-index)
            # 5: 2 (uint16)> alternate group id (in other atoms; 0 indicates not alternate)
            # 6: 2 (fixed16)> volume; 1.0 indicates normal volume
            #    2> reserved
            #    36 (9 x fixed32)> mapping of points from one coordinate space into another
            # 7: 4 (fixed32)> track width (pixels)
            # 8: 4 (fixed32)> track height (pixels)
            values = unpack('>x3x3I4xI8x2Hh2x36x2I', value)
            if values[5] == 0 and values[7] and values[8]:
                value = { 'Width': values[7] // 65536, 'Height': values[8] // 65536 }
            #
            else:
                value = False
            #
        #
        elif tag == b'tref':
            # 4 (uint32)> size
            # 4 (string)> type
            # N (uint32 list): track IDs
            value = False # ignore for now
        #
        elif tag == b'trkn':
            # 1> version
            # 3> flags
            # 4> reserved
            # 4 (uint32)> track number
            value = int.from_bytes(value[8:], byteorder='little')
        #
        elif tag == b'vmhd':
            # 1> version
            # 3> flags
            # 2 (uint16)> graphics mode
            # 6 (3 x uint16)> opcolor (r, g, b)
            value = False # ignore for now
        #
        else:
            value = value[16:]
            try: value = value.decode('utf-8')
            except: pass
        #

        # add the parsed data into the dictionary
        if value:
            if not isinstance(value, dict): value = { key: value }
            for key, value in value.items():
                if key in self:
                    if isinstance(self[key], list): self[key].append(value)
                    else: self[key] = [self[key], value]
                #
                else:
                    self[key] = value
                #
            #
        #
    # end _save
# end Mp4Parser

#--------------------------------------------------------------------------------------------------
# @brief Convert a date to an integer number of days for comparing.
# @param date - date string to convert (YYYY-MM-DD)
# @return a number used for sorting
def date2int(date):
    try:
        y, m, d = date.split('-')
        return (int(y) - 1900) * 400 + int(m) * 40 + int(d)
    #
    except:
        return 0
    #
# end date2int

#--------------------------------------------------------------------------------------------------
# @brief Main thread for scanning media files and logging the results.
class Worker(QThread):
    titleChanged  = pyqtSignal(str) # rich text string when the status title changes
    statusUpdate  = pyqtSignal(int, int, str, int) # processed, total, filename, remaining [seconds]
    criticalError = pyqtSignal(str) # error text
    complete      = pyqtSignal()

    #----------------------------------------------------------------------------------------------
    # @brief Contruct a worker thread to scan a directory recursively and process media files.
    # @param directory - top most directory to scan for media files
    def __init__(self, directory):
        super(Worker, self).__init__()
        self._paused    = False
        self._stopped   = False
        self._directory = directory
    # end constructor

    #----------------------------------------------------------------------------------------------
    # @brief Main run method for a QThread.
    def run(self):
        unique = lambda x: list(set(x))
        directory = self._directory

        # scan for a list of videos
        basename = os.path.basename(directory) or directory
        title = f'Scanning <a href="file:///{directory}">{basename}</a> for media files'
        self.titleChanged.emit(title)
        videos = []
        for root, directories, filenames in os.walk(directory):
            if r'\$RECYCLE.BIN' in root: continue
            for filename in filenames:
                ext = os.path.splitext(filename)[1].lower()
                if ext in ['.mp4', '.m4a']: videos.append(os.path.join(root, filename))
            #
        #

        # setup before parsing
        total = len(videos)
        title = f'Processing {total:,} files from <a href="file:///{directory}">{basename}</a>'
        self.titleChanged.emit(title)

        for d in ['covers', 'desc']:
            if not os.path.exists(d): os.mkdir(d)
        #

        tvFields    = ['Rating', 'Width', 'Height', 'Released', 'TV station']
        movieFields = ['Title', 'Directors', 'Cast', 'Genre', 'Rating', 'Width', 'Height',
                       'Duration', 'Released']

        movies = {} # unique key -> details dictionary
        tv     = {} # unique key -> details dictionary

        # process the data files
        start = time()
        for i, file in enumerate(videos):
            if self._stopped: break
            if self._paused:
                correction = time()
                while self._paused: sleep(0.1)
                start += time() - correction
            #

            # provide the status
            elapsed   = time() - start
            remaining = ((total * elapsed) / i) - elapsed if i > 0 else -1 # -1 is unknown
            self.statusUpdate.emit(i, total, os.path.basename(file), remaining)

            # process the file
            try:
                r = Mp4Parser(file)
                cover = None # filename to save cover art if available
                desc  = None # filename to write the long description

                if 'TV show' in r:
                    # Note: {Title} is like an overall title; often one of the following:
                    #       "{TV show}"
                    #       "{TV show} - {Episode title}"
                    #       "{TV show} - s{TV season}e{TV episode} - {Episode title}"
                    season   = r.get('TV season',  0)
                    episode  = r.get('TV episode', 0)
                    released = r.get('Released',   '')

                    key = '{0}: {1}'.format(season, r['TV show'])
                    if key in tv:
                        entry = tv[key]
                    #
                    else:
                        id = md5(key.encode('utf-8')).hexdigest()

                        entry = { 'ID':       id,
                                  'Cover':    0, # episode number used for cover (delete later)
                                  'Title':    r['TV show'],
                                  'Season':   season,
                                  'Released': released,
                                  'Duration': 0,   # [seconds]
                                  'Episodes': {},  # episode -> dictionary
                                  'Genre':    [],  # unique list of genres
                                  'Cast':     [] } # list of cast (not unique, yet)
                        for field in tvFields: entry[field] = r.get(field, '')

                        tv[key] = entry
                    #

                    # this allows covers to be saved for specials, especially when there are only
                    # specials, but take the cover for an actual episode when available
                    if not entry['Cover']:
                        cover = os.path.join('covers', '{0}.jpg'.format(entry['ID']))
                        entry['Cover'] = episode
                    #

                    # accumulate details
                    entry['Duration'] += r.get('Duration', 0)
                    entry['Genre']     = unique(entry['Genre'] + r.get('Genre', []))
                    entry['Cast']     += r.get('Cast', [])
                    entry['Episodes'][episode] = { 'Title':    r.get('Episode title', f'Episode #{episode}'),
                                                   'Duration': r.get('Duration', 0),
                                                   'Released': released }

                    # keep the earliest release date for the whole season
                    if date2int(released) < date2int(entry['Released']):
                        entry['Released'] = released
                    #
                #
                else:
                    # do not show duplicates, which generally happen for the following reasons:
                    # 1. a multidisc set that each have an MP4 file
                    # 2. a alternate ending/extended/director's cut version
                    key = '{0} {1}'.format(r['Released'][0:4], r['Title'])
                    if key in movies: continue

                    # extract the fields used by the web script
                    id    = md5(key.encode('utf-8')).hexdigest()
                    cover = os.path.join('covers', f'{id}.jpg')
                    desc  = os.path.join('desc', f'{id}.txt')

                    entry = { 'ID': id }
                    for field in movieFields: entry[field] = r.get(field, '')

                    # determine the path
                    path, name = os.path.split(file)
                    entry['Path'] = '{}/{}'.format(os.path.basename(path), name)

                    # limit the number of entries for some fields
                    for field, limit in { 'Directors': 2, 'Cast': 5 }.items():
                        if not field in entry: entry[field] = []
                        if not isinstance(entry[field], list): entry[field] = [entry[field]]
                        if len(entry[field]) > limit: entry[field] = entry[field][0:limit]
                    #

                    movies[key] = entry
                #

                # save the cover art
                if cover and 'Cover' in r:
                    im = Image.open(BytesIO(r['Cover']))
                    im.thumbnail((400, 400), Image.ANTIALIAS)
                    im.save(cover, 'JPEG')
                    del r['Cover']
                #

                # save the description
                if desc and 'Description' in r:
                    d = r['Description']
                    if isinstance(d, list): d = max(d, key=len)
                    with open(desc, 'w', encoding='utf-8') as fd: fd.write(d)
                #
            #
            except Exception as e:
                _, _, tb = sys.exc_info()
                msg = '{0}: {1} on line #{2}\nProcessing {3}'.format(type(e).__name__, str(e), tb.tb_lineno, file)
                self.criticalError.emit(msg)
                return
            #
        # end for

        # select the top 5 most used cast members for an entire season for TV shows
        # also remove the cover key
        for entry in tv.values():
            counts = {} # name -> number of occurances
            for name in entry['Cast']: counts[name] = counts.get(name, 0) + 1
            tmp = sorted(counts.items(), key=lambda x: -x[1])
            cast = [x[0] for x in tmp]

            if len(cast) > 5: cast = cast[0:5]
            entry['Cast'] = cast

            if 'Cover' in entry: del entry['Cover']
        #

        if movies:
            with open('.movies.txt', 'w') as fd:
                json.dump(list(movies.values()), fd)
            #
        #

        if tv:
            with open('.tv.txt', 'w') as fd:
                json.dump(list(tv.values()), fd)
            #
        #

        self.complete.emit()
    # end run

    #----------------------------------------------------------------------------------------------
    # @brief Accessor for the paused state.
    # @return True if paused, False otherwise
    def paused(self):
        return self._paused
    # end paused

    #----------------------------------------------------------------------------------------------
    # @brief Pause the processing thread.
    def pause(self):
        self._paused = True
    # end pause

    #----------------------------------------------------------------------------------------------
    # @brief Resume the processing thread.
    def resume(self):
        self._paused = False
    # end resume

    #----------------------------------------------------------------------------------------------
    # @brief Cancel the processing thread.
    def cancel(self):
        self._stopped = True
    # end cancel
# end Worker

#--------------------------------------------------------------------------------------------------
# @brief Main GUI window for the GUI application.
class MainWindow(QDialog):
    #----------------------------------------------------------------------------------------------
    # @brief Construct the main GUI window.
    def __init__(self):        
        super(MainWindow, self).__init__()
        self.setWindowTitle('Video meta data extractor')

        icon = b'iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAQAAAC1+jfqAAAAAmJLR0QA/4ePzL8AAADgSURBVCjPfY6' \
             + b'7SgNhEEZPNioGBCHaxV6wTBeQiDeEmIWwEoTUFgoG1FqwFkQQwcoqiI1a+Aj6DIIQ2FKIlbdKLI6FCl' \
             + b'7Wf77yOzNzIGvyTHPEPYt/qwFiOqOPJ86LnH+vIqocNh9iMfHS4hMdFj6qfuLh08ozjvlmTXocMEn+a' \
             + b'3OWO+y6LxZfSmc0GPz5dQoLrr+WLkgoZBnv7Lkq28xlZgLamybOmFoTK6YuiWVTWyLHEJFi07Y5seGG' \
             + b'kVh3y75PAG7w3/wGll0xFwLW1CtHQsCt1dCFcYfCDtmS1wFg9x0S7r2XC2tAyQAAAABJRU5ErkJggg=='
        pixmap = QPixmap()
        pixmap.loadFromData(QByteArray.fromBase64(icon))
        self.setWindowIcon(QIcon(pixmap))

        self._title    = None # banner title
        self._percent  = None # percent complete text
        self._button   = None # pause/resume button
        self._progress = None # progress bar
        self._filename = None # current filename being processed
        self._time     = None # time remaining
        self._items    = None # items remaining
        self._taskbar  = None # taskbar progress in Windows
        self._thread   = None # worker thread

        # create the main layout
        self.setLayout(QVBoxLayout())
        self.layout().setContentsMargins(16, 8, 16, 16)
        self.layout().setSpacing(4)

        # status text
        self._title = QLabel('Select a directory to scan')
        self._title.setTextFormat(Qt.RichText)
        self._title.linkActivated.connect(os.startfile)
        self.addWidgets(self._title)

        # percent complete and controls
        self._percent = QLabel('Idle')
        self._percent.setStyleSheet('font: 11pt')

        self._button = QPushButton(self.style().standardIcon(QStyle.SP_MediaPause), '')
        self._button.setFlat(True)
        self._button.clicked.connect(self._pauseResume)

        stop = QPushButton(self.style().standardIcon(QStyle.SP_MediaStop), '')
        stop.setFlat(True)
        stop.clicked.connect(self.close)

        self.addWidgets([self._percent, None, self._button, QLabel('  '), stop])

        # progress bar
        self._progress = QProgressBar()
        self._progress.setTextVisible(False)
        self._progress.setRange(0, 0)
        self.addWidgets(self._progress)

        # current file being processed
        label = QLabel('Name:')
        label.setFixedSize(label.sizeHint())
        self._filename = QLabel()
        self.addWidgets([label, self._filename])

        # time remaining
        label = QLabel('Time remaining:')
        label.setFixedSize(label.sizeHint())
        self._time = QLabel()
        self.addWidgets([label, self._time])

        # items remaining
        label = QLabel('Items remaining:')
        label.setFixedSize(label.sizeHint())
        self._items = QLabel()
        self.addWidgets([label, self._items])

        # window setup
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.setWindowFlags(Qt.MSWindowsFixedSizeDialogHint)
        self.setFixedWidth(425)
        self.setFixedHeight(max(self.sizeHint().height(), 150))

        # create the taskbar progress if on Windows 7+
        try:
            self._taskbar = QtWinExtras.QWinTaskbarButton(self)
            self._taskbar.progress().setRange(0, 0)
        #
        except:
            self._taskbar = None
        #
    # end constructor

    #----------------------------------------------------------------------------------------------
    # @brief Override the show method to start processing.
    def show(self):
        super(MainWindow, self).show()

        # determine the directory to scan
        directory = QFileDialog.getExistingDirectory(self, 'Select a media directory')
        if not directory: self.close()
        directory = os.path.abspath(directory)

        # start the thread
        self._thread = Worker(directory)
        self._thread.titleChanged.connect(self._title.setText)
        self._thread.statusUpdate.connect(self._update)
        self._thread.criticalError.connect(self._error)
        self._thread.complete.connect(self.close)
        self._thread.start()
    # end show

    #----------------------------------------------------------------------------------------------
    # @brief Convenience method to add widgets to the layout.
    # @param widgets - list of widgets to add, None means stretch
    def addWidgets(self, widgets):
        if not isinstance(widgets, list): widgets = [widgets]
        row = QHBoxLayout()
        for widget in widgets:
            if widget is None: row.addStretch()
            else: row.addWidget(widget)
        #
        self.layout().addLayout(row)
    # end addWidgets

    #----------------------------------------------------------------------------------------------
    # @brief Pause or resume processing.
    def _pauseResume(self):
        if not self._thread: return
        paused = self._thread.paused()
        icon = QStyle.SP_MediaPause if paused else QStyle.SP_MediaPlay
        self._button.setIcon(self.style().standardIcon(icon))

        if self._taskbar:
            if paused: self._taskbar.progress().resume()
            else: self._taskbar.progress().pause()
        #
        self._thread.resume() if paused else self._thread.pause()
        if not paused: self._percent.setText('Paused - ' + self._percent.text())
    # end _pauseResume

    #----------------------------------------------------------------------------------------------
    # @brief Update the display with live status.
    # @param processed - number of files processed
    # @param total - total number of files to process
    # @param filename - current filename being processed
    # @param remaining - estimate of the time remaining [seconds]
    def _update(self, processed, total, filename, remaining):
        # determine a friendlier way to show the time remaining
        if remaining < 0:
            remaining = 'calculating'
        #
        elif remaining >= 3570: # above 1 hour (0:59:30), only show hours and minutes
            increment = 5 # resolution in minutes to show
            mins = ceil(remaining / (increment * 60)) * increment
            hours, mins = divmod(mins, 60)

            remaining = 'About {0} hour{1}'.format(hours, 's' if hours != 1 else '')
            if mins > 0: remaining += f' {mins} minutes' # minutes cannot be 1, always use 's'
        #
        else: # between 0:00:00 and 0:59:30
            increment = 15
            remaining = max(increment, ceil(remaining / increment) * increment)
            mins, secs = divmod(remaining, 60)
            if remaining > 585: # above 0:09:45 show only minutes
                remaining = '{0} minutes'.format(max(10, mins))
            #
            else:
                remaining = 'About'
                if mins > 0: remaining += ' {0} minute{1}'.format(mins, 's' if mins != 1 else '')
                if secs > 0: remaining += f' {secs} seconds' # seconds cannot be 1, always use 's'
            #
        #

        # ensure the progress bars have the proper range set
        if self._progress.maximum() == 0: # not set
            self._progress.setRange(0, total)
            if self._taskbar:
                self._taskbar.setWindow(self.windowHandle())
                self._taskbar.progress().setRange(0, total)
                self._taskbar.progress().show()
            #
        #

        self._percent.setText('{0:.0f}% complete'.format(processed / total * 100))
        self._progress.setValue(processed)
        if self._taskbar: self._taskbar.progress().setValue(processed)
        self._filename.setText(filename)
        self._time.setText(remaining)
        self._items.setText('{0:,d}'.format(total - processed))
    # end _update

    #----------------------------------------------------------------------------------------------
    # @brief Handle critical errors.
    # @param msg - error message
    def _error(self, msg):
        QMessageBox.critical(self, 'Critical error', msg)
        self.close()
    # end _error

    #----------------------------------------------------------------------------------------------
    # @brief Handle the event when the user asks to close the main window.
    # @param event - event object
    def closeEvent(self, event):
        self.setEnabled(False)
        self.setCursor(QCursor(Qt.WaitCursor))

        if self._thread:
            self._thread.cancel()
            self._thread.wait()
        #

        event.accept()
    # end closeEvent
# end MainWindow

#--------------------------------------------------------------------------------------------------
# @brief Main application entry point.
if __name__ == '__main__':
    app = QApplication(sys.argv)
    main = MainWindow()
    main.show()
    sys.exit(app.exec_())
# end main

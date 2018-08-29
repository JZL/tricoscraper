"""Scraper for trico.haverford.edu

Written by Kei Imada

Last updated on 20180815

Todo:
    * ssl connections for the scraping?

To kill scraping midway through:
    ps aux|grep python|grep tricoscraper|awk '{prinit $2}'|xargs kill

"""


import bs4
import certifi
import requests
import itertools
import urllib3 as urllib
import multiprocessing as multi
import re
import json

from tricoinfo import TricoInfo
from tricoglobals import TRICO_URL, TRICO_PREFIX
from pdb import set_trace


def _TricoScraper_HTML_to_JSON(c, has_DT=False, DT_index=0):
    """
    Converts c, a dictionary with keys from the HTML scraper, and transform
    into the dictionairy with keys needed for the scheduler.

    has_DT allows datetime information to be added to the dict, if available.
    
    DT_index allows control over which DT is used (can be multiple)

    TODO: Don't allow get's silent "" replacement for critical fields
    """
    new_dict = {
        'name':     '{} {}'.format(c.get('subj', ""),c.get('num', "")),
        "comment":  c.get('comment', ""),
        "id":       c.get('CRN', ""),
        "ref":      c.get('CRN', ""),
        "subj":     "{} ({})".format(c.get('Department', ""), c.get('Subj', "")),
        "num":      c.get('Num', ""),
        "sec":      c.get('Sec', ""),
        "title":    c.get('Course Title', ""),
        "cred":     c.get('Credit', ""),
        "dist":     c.get('DIST', ""),
        "lim":      c.get('LIM', ""),
        "instruct": c.get('Instructor', "STAFF"),
        "rm":       c.get('Room Location', ""),
       # Not in html
       #"dpt":      "MLLD"
       #"type":    "Language",
    }
    if has_DT:
        new_dict["days"]  = c['DT'][DT_index]['day_str']
        new_dict["time"]  = c['DT'][DT_index]['time_str']
        new_dict["start"] = c['DT'][DT_index]['start_end_time'][0]
        new_dict["end"]   = c['DT'][DT_index]['start_end_time'][1]
        new_dict["dow"]   = c['DT'][DT_index]['dow']

    return new_dict

def _TricoScraper_collate_classes(classes):
    """
    Converts a list of classes (from the scraper) into a list of dicts for the scheduler front-end
    This list has different items depending on if it's a normal item, one with 0 datetimes, one with multiple datetimes

    TODO
    cat out.json |sed "s/}, {/},\n{/g"|grep -Po '"[^"]*":'|sort|uniq -c|sort -nk1,1
    check to make sure every page has the required/assumed th
    230 "Lab Sections":
    707 "Instructor":
    729 "Miscellaneous Links":
    795 "Additional Course Info":
    795 "Campus":
    795 "Course Title":
    795 "Credit":
    795 "Department":
    795 "Registration ID":
    795 "Room Location":
    795 "Semester":
    795 "Time And Days":
    795 "url":

    instructor is optional (STAFF) and lab section (TODO)
    """

    # List of dicts of class:
    #  0: Normal classes
    #  1: Classes with no times
    #  2: 2nd time for classes with 2 times
    collated_list = [{}, {}, {}]

    # TODO: There are some classes which have 3+ meeting times
    # (https://trico.haverford.edu/cgi-bin/courseguide/cgi-bin/search.cgi?Swarthmore+Fall_2018+THEA+S+022+01)
    # But this is also unsupported by the xls and includes a comment already, so am not
    # supporting for now. Will break for these classes bc will only support 2/3
    # days but the one in the comment is of a random position
    for c in classes:
        if len(c['DT']) == 0:
            collated_list[1][c['CRN']] = _TricoScraper_HTML_to_JSON(c)
        elif len(c['DT']) == 1:
            collated_list[0][c['CRN']] = _TricoScraper_HTML_to_JSON(c, has_DT=True, DT_index=0)
        elif len(c['DT']) >= 2:
            collated_list[0][c['CRN']] = _TricoScraper_HTML_to_JSON(c, has_DT=True, DT_index=0)
            collated_list[2][c['CRN']] = _TricoScraper_HTML_to_JSON(c, has_DT=True, DT_index=1)

    return collated_list

def _TricoScraper_parse_datetime(dt):
    """
    Takes in a datetime string, dt, of the form `MWF 11:30am-12:20pm, ...` and
    converts it into list of dictionaries with days (as a list of day indices),
    and 24-hour time start/end

    @input string dt of form `MWF 11:30am-12:20pm, ...`
    @output array of parsed dates
    """
    outArray = []

    # Some classes have comma separated multiple times
    # If same day, elides the second date list
    # A few random classes *start* with ", " which messes everything up so replace
    dt_list = re.sub("^, ?", "", dt).split(",")

    # First days is optional bc, if is same day, doesn't include
    """
        Input: `MWF 11:30am-12:20pm`
        Group 1. `MWF `
        Group 2. `MWF`
        Group 3. `11`
        Group 4. `30`
        Group 5. `am`
        Group 6. `12`
        Group 7. `20`
        Group 8. `pm`
    """
    # Complicated bash script but gives the list of all Time and Days (pipe
    # through grep -o .|sort|uniq -c to see all characters used (shows rare
    # Sunday and Saturday)
    # js-beautify.js out.json|grep "Time And Days"|sed 's/^.*: "//g'|sed "s/^,
    # //"|sed 's/",//'|sed "s/,/\n/g"|grep -v "^$"|grep '^[^0]'|awk '{print $1}'

    day_to_num = {"M": 1,"T": 2,"W": 3,"TH": 4,"F": 5,"S": 6,"U": 0};

    # Returns "MTWTHFSU" as the only valid chars for days
    days_chars = "".join(day_to_num.keys())

    datetime_re = '^((['+days_chars+']*) )?([0-9]{2}):([0-9]{2})([ap]m)-([0-9]{2}):([0-9]{2})([ap]m)$'


    # Returns something like 'W|U|TH|T|S|M|F' which is a regex to match each
    # day key. The important part is that TH is before T (with a reverse sort)
    # so the regex will match both chars instead of short circuting to T
    days_re = "|".join(sorted(day_to_num.keys(), reverse=True))

    # Need to be out of the loop bc if the second time is on the same day,
    # doesn't write it, so the 2nd time needs to inherit
    days = None

    for d in dt_list:
        match = re.match(datetime_re, d)
        if match is None:
            raise ValueError("This date string is not parseable by the regex: '{}'".format(dt))

        # Check if has no date and the previous day (if it was comma separated)
        # didn't have one
        if match.group(2) is None:
            if days is None:
                raise ValueError("This date string has no days (MWF, etc): '{}'->{}".format(dt, dd))
            # Else: inherit from previous comma separated day
        else:
            days = match.group(2) 

        days_list = re.findall(days_re, days)

        # Sanity check that the days tokens found in days_list should contain
        # all characters in the original string
        if len(days) != len("".join(days_list)):
                raise ValueError("This date string's days (MWF) was not parsed correctly: '{}'".format(dt))

        days_number = [day_to_num[item] for item in days_list]


        start_end_time = []
        time_str = []

        # 3,6 is the group index of both hours (see above regex)
        for i in [3, 6]:
            time_str.append("{}:{} {}".format(match.group(i),
                match.group(i+1), match.group(i+2)))

            # 2 groups down from the hour is the am/pm
            am_pm = match.group(i+2)
            hour = int(match.group(i))

            if am_pm == "pm":
                # To add 12 to pm hours, need to make 12pm -> 0 before adding
                # 12 (military time is 0 indexed)
                if hour == 12:
                    hour = 0
                hour = hour+12
            # 1 group down from the hour is the minutes
            start_end_time.append("{}:{}".format(hour, match.group(i+1)))

        outArray.append({
            'time_str': "-".join(time_str),
            'day_str': " ".join(days_list),
            # TODO should not need to be a string but used with JSON.parse in
            # scheduler
            'dow': str(days_number),
            'start_end_time': start_end_time
        })

    return outArray
        

def _TricoScraper_get_links(params):
    """Gets list of links given the parameters for the GET request.

    Args:
        params (list of tuples of strings): the parameters for the GET request
                                            header.

    Returns:
        list of strings: links.

    """
    req = requests.get(TRICO_URL, params=params)
    soup = bs4.BeautifulSoup(req.text, 'html.parser')
    table = soup.find('table',
                      {'width': '100%', 'border': '2'})
    a_elements = table.findChildren('a')
    links = [TRICO_PREFIX+a['href'] for a in a_elements]
    return links


def _TricoScraper_get_course(url):
    """Given url, return dictionary containing course descriptions.

    Args:
        url (string): the url to the course page.

    Returns:
        dictionary: the course description.

    """
    req = requests.get(url)
    soup = bs4.BeautifulSoup(req.text, 'html.parser')
    course = {}
    # course key -> regular expression with group 1 being value
    # Assumes "DIST" is at the end of the line
    additional_info_keys = {
        'CRN': 'CRN: ([0-9]*)',
        'LIM': 'ENR LIM: ([0-9]*)',
        'CUR': 'CUR ENR: ([0-9]*)',
        'DIST': 'DIST: (.*)',
    }
    rows = soup.findChild('table').findChildren('tr')
    for row in rows:
        # The html.parser adds a closing </br> tag (against W3C spec :-( )
        # which becomes the parent of the text
        row.br.insert_before("\n")
        row.br.unwrap()

        [key, value] = [t.text for t in row.findChildren('td')]
        course[key.strip()] = value.strip()

        if key == "Additional Course Info":
            split_info = value.strip().split("\n")
            if len(split_info) == 0 or len(split_info) > 2:
                raise ValueError('Course has no lines or 3+ lines in additional course info ({})'.format(url))
            frst_val = split_info[0]
            for k in additional_info_keys:
                m = re.search(additional_info_keys[k], value) 
                if m is not None:
                    course[k] = m.group(1)
                else:
                    course[k] = ""
            if len(split_info) == 2:
                course['comment'] = " ".join(split_info[1:])
            else:
                course['comment'] = ''

    # Parse time and Days into start, end, days
    if course['Time And Days'] == '':
        course['DT'] = []
    else:
        course['DT'] = _TricoScraper_parse_datetime(course['Time And Days'])
    course['Subj'], course['Num'], course['Sec'] = course['Registration ID'].split()
    course['URL'] = url
    return course


class TricoScraper(object):
    """The scraper for trico.haverford.edu."""

    def __init__(self, num_threads=multi.cpu_count(), ssl=True):
        """Creates a TricoScraper Object.

        Args:
            num_threads (int): The number of worker threads. Defaults to number
                               of cores.
            ssl (bool): Whether or not to use secure connection. Defaults to
                        True (use ssl).

        """
        self._pool = multi.Pool(num_threads)
        if ssl:
            self._http = urllib.PoolManager(cert_reqs='CERT_REQUIRED',
                                            ca_certs=certifi.where())
        else:
            self._http = urllib.PoolManager()

    def _get_num_links(self, params):
        """Gets number of classes the search parameter hit.

        Args:
            params (list of tuples of strings): The search parameters.

        Returns:
            int: the number of classes the search parameter hit.

        """
        req = requests.get(TRICO_URL, params=params)
        soup = bs4.BeautifulSoup(req.text, 'html.parser')
        return int(soup.find('font').findChild('b').string.split(' ')[-1])

    def search(self,
               campus=None,
               crsnum=".",
               dept=None,
               instr=".",
               meetday=".",
               meettime=None,
               smstr=None,
               srch_frz="."):
        """Searches the trico.haverford.edu website for courses.

        Args:
            campus (list of strings): Campuses the courses are in. Defaults to
                                      None (all campuses).
            crsnum (string): Course number for a course. Defaults to "." (any
                             course number).
            dept (list of strings): Departments the courses are in. Defaults to
                                    None (all departments).
            instr (string): The instructor for the course. Defaults to "." (any
                            instructor).
            meetday (string): The days the courses are met. Defaults to "."
                              (any day).
            meettime (string): The times the courses are met. Defaults to None
                               (any time).
            smstr (list of strings): The semesters the courses are in. Defaults
                                     to None (all semesters).
            srch_frz (string): I don't know what this is. Defaults to "."

        Returns:
            list of dictionaries: list of course descriptions

        """
        # Input processing
        if None in [smstr, campus, dept]:
            ti = TricoInfo()
        if smstr is None:
            smstr = ti.semesters
        if campus is None:
            campus = ti.campuses
        if dept is None:
            dept = ti.departments

        # Creating the search parameters
        params = [
            (".cgifields", "campus,dept,smstr,meettime"),
            ("Search", "Search"),
            ("crsnum", crsnum),
            ("instr", instr),
            ("meetday", meetday),
            ("srch_frz", srch_frz)
        ]
        params += [("smstr", s) for s in smstr]
        params += [("campus", c) for c in campus]
        params += [("dept", d) for d in dept]
        if meettime is not None:
            params += [("meettime", m) for m in meettime]

        # Get course page links
        num_links = self._get_num_links(params)
        paramss = [params[:]+[("run_tot", str(i))] for i in
                   range(0, num_links, 50)]
        linkss = self._pool.map(_TricoScraper_get_links, paramss)
        links = list(itertools.chain.from_iterable(linkss))

        # Get course descriptions
        courses = self._pool.map(_TricoScraper_get_course, links)
        return courses

def read_from_cache():
    """
    If don't want to scrape, but want to generated collated scraped data
    """
    f = open("out_scraped.json", "r")
    inp = json.load(f)

    res = json.dumps(_TricoScraper_collate_classes(inp))
    f = open("out_collate.json", "w+")
    f.write(res)

def main():
    ts = TricoScraper()

    # Note: Bryn mawr/haverford have differnt
    # db structures (i.e. bryn mawr has
    # "Class Number" not CRN) so the collation
    # for the scheduler will not work
    ts_search = ts.search(smstr=['Fall_2018'], campus=["Swarthmore"])
    result = json.dumps(ts_search)

    f = open("out_scraped.json", "w+")
    f.write(result)

    read_cache()

if __name__ == '__main__':
    # For debugging can use cache to not scrape
    make_new = True
    if make_new:
        main()
    else:
        read_cache()

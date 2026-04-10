from cProfile import label
import csv
from operator import index
from pathlib import Path
import sys
import os
import matplotlib.pyplot as plt
import matplotlib.image as mpimg
from matplotlib.widgets import TextBox, Button
import numpy as np
import unicodedata
import math
from collections import Counter
import time

#set up user variables for input
enteredCity = ""
cityPop = 0
cityClass = ""
cityState = ""
cityLat = 0.0
cityLon = 0.0

#set up font sizes for different text elements on the image
NEW_FONT_PROMPT = 10
NEW_FONT_LIST = 8
NEW_FONT_INPUT = 8
NEW_FONT_BUTTON = 8

#set up lists to hold city data
listOfCityStates = []
listOfCityClasses = []
listOfCityNames = []
listOfCityPops = []
listOfCityLats = []
listOfCityLongs = []
popmax = 0

#set up lists to hold cities that have been guessed
guessedCityStates = []
guessedCityClasses = []
guessedCityNames = []
guessedCityPops = []
guessedCityLats = []
guessedCityLongs = []
top10_largest = []     # sorted descending by population
top10_smallest = []    # sorted ascending by population (excluding pop=0)
cached_sorted_states = []
# Best States Variables
state_guess_counter = Counter()
best_states_artist = None
best_states_expanded = False
best_states_scroll = 0
best_states_items_per_page = 20

#all state abbreviations for user input validation
stateAbbreviations = {
    "CP": "Huntington",
    "HU": "Huntington",
    "04": "AR120-04",
    "05": "AR120-05",
    "WH": "Whitestone",
    "RP": "Ruppacke",
    "AD": "Ardelia",
    "PQ": "Penquisset",
    "NC": "New Carnaby",
    "WR": "Wiarni",
    "PA": "Passamaqueets",
    "HY": "Hyde",
    "AS": "Astrantia",
    "RM": "Rougemont",
    "OP": "Opelika",
    "OC": "Orange Coast",
    "LN": "Laine",
    "EU": "Eustacia",
    "OG": "Ogdalen",
    "27": "AR120-27",
    "28": "AR120-28",
    "MC": "Michisaukee",
    "EM": "East Massodeya",
    "WM": "West Massodeya",
    "GN": "Gnaerey",
    "PS": "Passitania",
    "WA": "Wauseka",
    "37": "AR120-37",
    "MG": "Minnesaugiaw",
    "39": "AR120-39",
    "DP": "Des Plaines",
    "ME": "Mennowa",
    "ZH": "Zakahigan",
    "TE": "Tennewa",
    "WY": "Wychelle",
    "IL": "Illuvia",
    "MI": "Mishota",
    "IR": "Iroquesia",
    "SN": "Seneppi",
    "MN": "Minnonigan",
    "56": "AR120-56",
    "VE": "Venary",
    "MK": "Makaska",
    "WI": "Wisecota",
    "RS": "Riopoderos",
    "AW": "Apawiland",
    "73": "AR120-73",
    "AC": "Alcortez",
    "SR": "Sierra",
    "CL": "Clamash",
    "TA": "Tauhon",
    "82": "AR120-82",
    "CO": "Cosperica",
    "TM": "Tempache",
    "87": "AR120-87",
    "AL": "Alormen",
    "Huntington": "CP",
    "AR120-04": "-04",
    "AR120-05": "-05",
    "Whitestone": "WH",
    "Ruppacke": "RP",
    "Ardelia": "AD",
    "Penquisset": "PQ",
    "New Carnaby": "NC",
    "Wiarni": "WR",
    "Passamaqueets": "PA",
    "Hyde": "HY",
    "Astrantia": "AS",
    "Rougemont": "RM",
    "Opelika": "OP",
    "Orange Coast": "OC",
    "Laine": "LN",
    "Eustacia": "EU",
    "Ogdalen": "OG",
    "AR120-27": "-27",
    "AR120-28": "-28",
    "Michisaukee": "MC",
    "East Massodeya": "EM",
    "West Massodeya": "WM",
    "Gnaerey": "GN",
    "Passitania": "PS",
    "Wauseka": "WA",
    "AR120-37": "-37",
    "Minnesaugiaw": "MG",
    "AR120-39": "-39",
    "Des Plaines": "DP",
    "Mennowa": "ME",
    "Zakahigan": "ZH",
    "Tennewa": "TE",
    "Wychelle": "WY",
    "Illuvia": "IL",
    "Mishota": "MI",
    "Iroquesia": "IR",
    "Seneppi": "SN",
    "Minnonigan": "MN",
    "AR120-56": "-56",
    "Venary": "VE",
    "Makaska": "MK",
    "Wisecota": "WI",
    "Riopoderos": "RS",
    "Apawiland": "AW",
    "AR120-73": "-73",
    "Alcortez": "AC",
    "Sierra": "SR",
    "Clamash": "CL",
    "Tauhon": "TA",
    "AR120-82": "-82",
    "Cosperica": "CO",
    "Tempache": "TM",
    "AR120-87": "-87",
    "Alormen": "AL"
}

#set up global variables for scatter artist
scatter_artist = None
scatter_x = []
scatter_y = []
scatter_sizes = []

# Panning state
is_panning = False
pan_start = None
pan_xlim = None
pan_ylim = None

# GUI state for when multiple matches require a state abbreviation
pending_city_for_state = None
pending_available_states = []

# Loads the city data from the CSV file into lists, and builds lookup dictionaries for efficient searching by city name and city+state.
def resource_path(relative_path):
    # Always prefer local file first
    local_path = os.path.abspath(relative_path)
    if os.path.exists(local_path):
        return local_path

    # Fallback to PyInstaller bundle
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")

    return os.path.join(base_path, relative_path)
#path for files
csv_path = Path(resource_path("FSA Cities.csv"))
state_lines_path = Path(resource_path("State Lines.png"))

# create on-figure prompt, a scrollable guessed list area, and input TextBox with scroll buttons
guessed_list_artist = None
text_artist = None
guessed_scroll_start = 0
items_per_page = 6  # visible lines in the guessed list window
recent_guesses_artist = None #artist for displaying the last 3 guesses in reverse chronological order at the top-left of the figure, next to the TextBox
top10_largest_artist = None  # new artist for top 10 largest guessed cities
smallest10_artist = None # new artist for smallest 10 guessed cites (non-zero)
# Sorting state for final list
sort_button = None
current_sort_mode = "Guess Order"
sort_modes = ["Guess Order", "Alphabetical", "Population"]

# converts ints safely
def safe_int(val):
    try:
        return int(val)
    except:
        try:
            return int(float(val))
        except:
            return 0

#appends the city data to the guessed city lists based on the index of the city name in the main list
def appendGuessedCity(city):
    """
    Append a guessed city by name. If multiple entries with same name exist,
    pick the first one that has NOT already been guessed (same city+state).
    If all city+state combinations for that name were already guessed, show a message.
    """
    name = city.strip()
    match_indices = [i for i, n in enumerate(listOfCityNames) if n.lower() == name.lower()]
    if not match_indices:
        show_message(f"{name.title()} not found in city list.")
        return False
    for i in match_indices:
        st = listOfCityStates[i]
        if not has_already_guessed(listOfCityNames[i], st):
            appendGuessedByIndex(i)
            return True
    # all matching city/state combos already guessed
    show_message(f"You have already guessed {name.title()} for every available state in the list.")
    return False
# append by index helper (safer than using name lookups)
def appendGuessedByIndex(index):
    guessedCityNames.append(listOfCityNames[index])
    guessedCityStates.append(listOfCityStates[index])
    guessedCityClasses.append(listOfCityClasses[index])
    guessedCityPops.append(listOfCityPops[index])
    guessedCityLats.append(listOfCityLats[index])
    guessedCityLongs.append(listOfCityLongs[index])
    state_guess_counter[listOfCityStates[index]] += 1
    # -----------------------------
    # Incremental top 10 tracking
    # -----------------------------
    global top10_largest, top10_smallest

    new_entry = {
        "name": listOfCityNames[index],
        "state": listOfCityStates[index],
        "pop": listOfCityPops[index]
    }

    # ----- LARGEST (descending) -----
    inserted = False
    for i, city in enumerate(top10_largest):
        if new_entry["pop"] > city["pop"]:
            top10_largest.insert(i, new_entry)
            inserted = True
            break

    if not inserted:
        top10_largest.append(new_entry)

    if len(top10_largest) > 10:
        top10_largest = top10_largest[:10]


    # ----- SMALLEST (ascending, exclude 0) -----
    if new_entry["pop"] > 0:

        inserted = False
        for i, city in enumerate(top10_smallest):
            if new_entry["pop"] < city["pop"]:
                top10_smallest.insert(i, new_entry)
                inserted = True
                break

        if not inserted:
            top10_smallest.append(new_entry)

        if len(top10_smallest) > 10:
            top10_smallest = top10_smallest[:10]

    # plot a red marker on the map for this guessed city (if figure available)
    try:
        lat = float(listOfCityLats[index])
        lon = float(listOfCityLongs[index])
    except Exception:
        lat = None
        lon = None

    if lat is not None and lon is not None and 'fig' in globals() and 'ax' in globals():
        try:
            if _has_geo_transform:
                xpix, ypix = latlon_to_xy(lat, lon)
            else:
                # fallback: attempt simple linear rescale using image extents
                im_h, im_w = img.shape[0], img.shape[1]
                lons = [p[1] for p in _cal_points]
                lats = [p[0] for p in _cal_points]
                lon_min, lon_max = min(lons), max(lons)
                lat_min, lat_max = min(lats), max(lats)
                xpix = (lon - lon_min) / (lon_max - lon_min) * (im_w - 1)
                ypix = (lat - lat_min) / (lat_max - lat_min) * (im_h - 1)

            # -----------------------------
            # Population-based marker sizing (piecewise linear)
            # -----------------------------

            # Base marker size for the largest city (pop_max = 8,501,861), define key populations
            pop_max = 8_501_861    # Stanton
            pop_500k = 500_000
            pop_100k = 100_000
            pop_20k = 20_000
            pop_0 = 0

            # define areas
            max_area = 600.0       # Stanton
            area_500k = max_area / 3         # 1/3 of Stanton
            area_100k = area_500k / 3         # 1/3 of 500k
            area_20k = area_100k / 3          # 1/3 of 100k
            area_0 = area_20k / 3              # 1/3 of 20k

            pop_val = listOfCityPops[index]

            if pop_val <= pop_0:
                area = area_0
            elif pop_val <= pop_20k:
                slope = (area_20k - area_0) / (pop_20k - pop_0)
                area = area_0 + slope * (pop_val - pop_0)
            elif pop_val <= pop_100k:
                slope = (area_100k - area_20k) / (pop_100k - pop_20k)
                area = area_20k + slope * (pop_val - pop_20k)
            elif pop_val <= pop_500k:
                slope = (area_500k - area_100k) / (pop_500k - pop_100k)
                area = area_100k + slope * (pop_val - pop_100k)
            else:
                slope = (max_area - area_500k) / (pop_max - pop_500k)
                area = area_500k + slope * (pop_val - pop_500k)

            #add marker to the scatter artist's data and redraw
            # Add marker to internal lists
            scatter_x.append(xpix)
            scatter_y.append(ypix)
            scatter_sizes.append(area)

            # Build offsets from authoritative Python lists
            new_offsets = np.column_stack((scatter_x, scatter_y))
            scatter_artist.set_offsets(new_offsets)

            # Always set sizes from authoritative list
            scatter_artist.set_sizes(np.array(scatter_sizes))
        except Exception:
            # silently ignore plotting errors to avoid breaking the game
            pass

    update_guessed_list()
    update_recent_guesses()
    update_top10_largest_guessed()
    update_smallest10_guessed()
    global cached_sorted_states
    cached_sorted_states = sorted(
        state_guess_counter.items(),
        key=lambda x: x[1],
        reverse=True
    )
    update_best_states()
    return
#standardizes city names for comparison by removing accents, lowercasing, replacing hyphens, and standardizing common prefixes
def canonical_city(text):

    if not isinstance(text, str):
        return ""

    # Remove accents (e.g., Hálison -> Halison)
    text = unicodedata.normalize('NFKD', text)
    text = ''.join(c for c in text if not unicodedata.combining(c))

    # Lowercase
    text = text.lower()

    # Replace hyphens with spaces
    text = text.replace("-", " ")

    # Standardize Saint/St
    text = text.replace("saint", "st")
    text = text.replace("st.", "st")

    # Standardize Fort/Ft
    text = text.replace("fort", "ft")
    text = text.replace("ft.", "ft")

    # Collapse multiple spaces
    text = " ".join(text.split())

    return text.strip()
# build display string for a found city index
def city_info_for_index(index):
    return f"{listOfCityNames[index]} is a {listOfCityClasses[index]} class city in {listOfCityStates[index]} with a population of {listOfCityPops[index]}, located at latitude {listOfCityLats[index]} and longitude {listOfCityLongs[index]}."
#implements scrolling mechanism for guessed cities list if it exceeds the visible area
def clamp_scroll():
    global guessed_scroll_start
    total = len(guessedCityNames)
    if total <= items_per_page:
        guessed_scroll_start = 0
    else:
        max_start = max(0, total - items_per_page)
        guessed_scroll_start = min(max(0, guessed_scroll_start), max_start)
# final message builder
def finish_game():
    total_population = 0
    try:
        total_population = sum(int(p) for p in guessedCityPops)
    except Exception:
        # fallback: attempt safe numeric conversion per item
        total = 0
        for p in guessedCityPops:
            try:
                total += int(p)
            except Exception:
                try:
                    total += int(float(p))
                except Exception:
                    pass
        total_population = total

    msg = f"You guessed {len(guessedCityNames)} cities!\nTotal population of guessed cities: {total_population:,}"
    show_message(msg, small_pause=2.5)

    # disable TextBox by clearing its value and disconnecting submit callback if present
    try:
        text_box.set_val("")  # clear
        try:
            text_box.disconnect(cid_submit)
        except Exception:
            # some backends/widgets may not support disconnect; ignore
            pass
    except Exception:
        pass

    # give user a moment to read the message
    # sort button at the end to allow them to sort their guesses after finishing
    global sort_button, current_sort_mode

    if sort_button is None:
        button_ax = fig.add_axes([0.02, 0.02, 0.16, 0.045])  # bottom-left
        button_ax.set_zorder(10)
        sort_button = Button(button_ax, f"Sort: {current_sort_mode}")

        def cycle_sort(event):
            global current_sort_mode
            current_index = sort_modes.index(current_sort_mode)
            next_index = (current_index + 1) % len(sort_modes)
            current_sort_mode = sort_modes[next_index]
            sort_button.label.set_text(f"Sort: {current_sort_mode}")
            update_guessed_list()
            fig.canvas.draw_idle()

        sort_button.on_clicked(cycle_sort)

    fig.canvas.draw_idle()
# check if a city+state pair has already been guessed (case-insensitive)
def has_already_guessed(city_name, state_abbr):
    """
    Return True if the exact city+state pair has already been guessed.
    city_name: string (case-insensitive)
    state_abbr: string (expected abbreviation, case-insensitive)
    """
    if city_name is None or state_abbr is None:
        return False
    name_l = city_name.lower()
    abbr_u = state_abbr.upper()
    for i, g in enumerate(guessedCityNames):
        if g.lower() == name_l and i < len(guessedCityStates) and guessedCityStates[i].upper() == abbr_u:
            return True
    return False
#checks if a variable is a list    
def isVariableList(var):
    return isinstance(var, list)
# submit callback for the TextBox
def on_submit(text):
    value = text.strip()

    if value == "":
        return

    text_box.set_val("")

    if value.lower() == "finish":
        finish_game()
        return

    result = searchCity(value)

    if result["status"] == "not_found":
        show_message(f"{value} is not in the list. Try again.")
        return

    idx = result["index"]

    if has_already_guessed(listOfCityNames[idx], listOfCityStates[idx]):
        show_message("You already guessed that city and state.")
        return

    appendGuessedByIndex(idx)

    show_message("Enter the name of a city. Enter 'finish' to end the game:")
#runs searchCity function with city prompted and prints response to user
def printResponse(cityName):
    city = searchCity(cityName)
    if city == "SEARCH CANCELLED":
        return "Search cancelled. Please enter a new city name."
    if city == "invalid":
        return f"{cityName.title()} is not in the list of cities for that state. Please try again."
    if isVariableList(city):
        index = listOfCityNames.index(city[0])
        return f"{city[0]} is a {listOfCityClasses[index]} class city in {city[1]} with a population of {listOfCityPops[index]}, located at latitude {listOfCityLats[index]} and longitude {listOfCityLongs[index]}."
    else:
        index = listOfCityNames.index(city)
        return f"{city} is a {listOfCityClasses[index]} class city in {listOfCityStates[index]} with a population of {listOfCityPops[index]}, located at latitude {listOfCityLats[index]} and longitude {listOfCityLongs[index]}."
#shows the prompt on the image and in the terminal
def prompt_city():
    """
    Update the image with the prompt and read input from the terminal.
    Shows the same prompt both on the 'State Lines.png' figure (if present)
    and in the terminal.
    """
    prompt = "Enter the name of a city. Enter 'finish' to end the game: "
    if text_artist is not None:
        text_artist.set_fontsize(NEW_FONT_PROMPT)
        text_artist.set_text(prompt.strip())
        try:
            fig.canvas.draw_idle()
        except Exception:
            pass
    return input(prompt).strip()
#searches for city name in list and returns city name if found.
def searchCity(user_input):
    """
    Handles:
    - "City"
    - "City, State"
    - "City, StateAbbreviation"
    """

    raw = user_input.strip()

    if not raw:
        return {"status": "not_found"}

    # ----------------------------------------
    # Case 1: User entered "City, Something"
    # ----------------------------------------
    if "," in raw:
        parts = raw.split(",", 1)
        city_part = parts[0].strip()
        state_part = parts[1].strip()

        city_norm = canonical_city(city_part)

        # Convert full state name to abbreviation if needed
        state_upper = state_part.upper()

        if state_part in stateAbbreviations:
            state_upper = stateAbbreviations[state_part]
        elif state_upper in stateAbbreviations:
            pass
        else:
            # Try matching full state name case-insensitive
            for key, val in stateAbbreviations.items():
                if val.lower() == state_part.lower():
                    state_upper = key
                    break

        key = (city_norm, state_upper.upper())

        if key in city_state_lookup:
            return {"status": "found", "index": city_state_lookup[key]}

        return {"status": "not_found"}

    # ----------------------------------------
    # Case 2: User entered only "City"
    # ----------------------------------------
    city_norm = canonical_city(raw)

    if city_norm not in city_lookup:
        return {"status": "not_found"}

    indices = city_lookup[city_norm]

    # Only one match
    if len(indices) == 1:
        return {"status": "found", "index": indices[0]}

    # Multiple matches → return precomputed best
    return {"status": "found", "index": city_best_index_lookup[city_norm]}
#shows message on image
def show_message(msg, small_pause=None):
    print(msg)
    if text_artist is not None:
        text_artist.set_fontsize(NEW_FONT_PROMPT)
        text_artist.set_text(msg)
    if small_pause is not None:
        plt.pause(small_pause)
# Updates the "Best States" list on the right panel, showing the states with the most guessed cities. Supports expansion to show more states and scrolling when expanded.
def update_best_states():
    global best_states_artist

    if best_states_artist is None:
        return

    if not state_guess_counter:
        best_states_artist.set_text("Best States\n\nNo guesses yet.")
        return

    # Full sorted ranking
    full_sorted_states = cached_sorted_states

    lines = ["Best States", ""]

    if not best_states_expanded:
        # Show top 5 only
        visible = full_sorted_states[:5]

        for i, (state, count) in enumerate(visible):
            lines.append(f"{i+1}. {state}: {count}")

    else:
        # Show up to top 20 with scrolling
        top_twenty = full_sorted_states[:20]

        total = len(top_twenty)
        window = best_states_items_per_page
        max_scroll = max(0, total - window)

        start = min(best_states_scroll, max_scroll)
        end = start + window

        visible = top_twenty[start:end]

        for rank, (state, count) in enumerate(visible, start=start+1):
            lines.append(f"{rank}. {state}: {count}")

    best_states_artist.set_text("\n".join(lines))
    best_states_artist.set_fontsize(NEW_FONT_LIST)

    over_1m, over_500k, over_100k, over_50k = get_population_guess_stats()
    def pct(part, total):
        return round((part / total) * 100) if total > 0 else 0
    stats_text = (
        f"Population Milestones\n\n"
        f"{over_1m} of {TOTAL_OVER_1M} over 1,000,000 ({pct(over_1m, TOTAL_OVER_1M)}%)\n"
        f"{over_500k} of {TOTAL_OVER_500K} over 500,000 ({pct(over_500k, TOTAL_OVER_500K)}%)\n"
        f"{over_100k} of {TOTAL_OVER_100K} over 100,000 ({pct(over_100k, TOTAL_OVER_100K)}%)\n"
        f"{over_50k} of {TOTAL_OVER_50K} over 50,000 ({pct(over_50k, TOTAL_OVER_50K)}%)"
    )
    population_stats_artist.set_text(stats_text)

# prepare an on-image prompt (if the figure exists)
def update_guessed_list():
    global guessed_list_artist, guessed_scroll_start

    if guessed_list_artist is None:
        return

    clamp_scroll()
    guessed_list_artist.set_fontsize(NEW_FONT_LIST)

    total = len(guessedCityNames)

    if total == 0:
        guessed_list_artist.set_text("No guesses yet.")
        return

    # ----------------------------------------
    # Build sorted index list
    # ----------------------------------------
    indices = list(range(total))

    if current_sort_mode == "Alphabetical":
        indices.sort(key=lambda i: guessedCityNames[i].lower())

    elif current_sort_mode == "Population":
        indices.sort(key=lambda i: guessedCityPops[i], reverse=True)

    # Guess Order = original order (do nothing)

    start = guessed_scroll_start
    end = min(start + items_per_page, total)

    visible_indices = indices[start:end]

    lines = []

    for rank, idx in enumerate(visible_indices, start=start+1):
        city = guessedCityNames[idx]
        state_abbr = guessedCityStates[idx]
        state_display = stateAbbreviations.get(state_abbr, state_abbr)
        pop = guessedCityPops[idx]

        try:
            pop_str = f"{int(pop):,}"
        except Exception:
            pop_str = str(pop)

        lines.append(f"{rank}. {city}, {state_display}: {pop_str}")

    footer = f"Showing {start+1}-{end} of {total}"
    guessed_list_artist.set_text("\n".join(lines + ["", footer]))
def update_top10_largest_guessed():
    global top10_largest, top10_largest_artist

    if top10_largest_artist is None or not largest_visible:
        return

    if not top10_largest:
        top10_largest_artist.set_text("Largest 10 guessed cities\n\nNo guesses yet.")
        return

    lines = ["Largest 10 guessed cities", ""]

    for i, city in enumerate(top10_largest):
        state_display = stateAbbreviations.get(city['state'], city['state'])
        pop_str = f"{int(city['pop']):,}"
        lines.append(f"{i+1}. {city['name']}, {state_display}: {pop_str}")

    top10_largest_artist.set_text("\n".join(lines))
    top10_largest_artist.set_fontsize(NEW_FONT_LIST)
#displays the last 3 guesses in reverse chronological order at the top-left of the figure, next to the TextBox
def update_recent_guesses():
    if recent_guesses_artist is None:
        return

    total = len(guessedCityNames)

    if total == 0:
        recent_guesses_artist.set_text("")
        return

    lines = []

    # Last 3 guesses (most recent first)
    start = max(0, total - 3)
    recent_indices = range(total - 1, start - 1, -1)

    for idx in recent_indices:
        city = guessedCityNames[idx]
        full_state = guessedCityStates[idx]
        # Convert full state name → abbreviation
        state_abbr = stateAbbreviations.get(full_state, full_state)
        pop = guessedCityPops[idx]
        try:
            pop_str = f"{int(pop):,}"
        except Exception:
            pop_str = str(pop)
        lines.append(f"{idx+1}. {city}, {state_abbr}: {pop_str}")

    recent_guesses_artist.set_fontsize(NEW_FONT_LIST)
    recent_guesses_artist.set_text("Recent Guesses:\n" + "\n".join(lines))
# displays the 10 smallest guessed cities (excluding population = 0) in middle left area, positioned between Recent Guesses and Largest 10
def update_smallest10_guessed():
    global top10_smallest, smallest10_artist

    if smallest10_artist is None or not smallest_visible:
        return

    if not top10_smallest:
        smallest10_artist.set_text("Smallest 10 guessed cities\n\nNo eligible guesses yet.")
        return

    lines = ["Smallest 10 guessed cities", ""]

    for i, city in enumerate(top10_smallest):
        state_display = stateAbbreviations.get(city['state'], city['state'])
        pop_str = f"{int(city['pop']):,}"
        lines.append(f"{i+1}. {city['name']}, {state_display}: {pop_str}")

    smallest10_artist.set_text("\n".join(lines))
    smallest10_artist.set_fontsize(NEW_FONT_LIST)
#open csv file and read data into lists
try:
    try:
        file = open(csv_path, 'r', newline='', encoding='utf-8', errors='replace')
    except Exception:
        file = open(csv_path, 'r', newline='', encoding='cp1252')

    with file:
        cityFile = csv.reader(file)
        next(cityFile, None)

        for line in cityFile:
            if len(line) >= 7:
                listOfCityStates.append(line[1].strip())
                listOfCityClasses.append(line[2].strip())
                listOfCityNames.append(line[3].strip())

                pop_raw = line[4].strip().replace(',', '')
                try:
                    listOfCityPops.append(int(pop_raw))
                except ValueError:
                    listOfCityPops.append(0)

                try:
                    listOfCityLats.append(float(line[5].strip()))
                except:
                    listOfCityLats.append(0.0)

                try:
                    listOfCityLongs.append(float(line[6].strip()))
                except:
                    listOfCityLongs.append(0.0)

except FileNotFoundError:
    print(f"CSV not found {csv_path}", file=sys.stderr)

# Precompute maximum population once (performance optimization)
try:
    pop_max = max(listOfCityPops) if listOfCityPops else 0
    all_city_pops = [safe_int(p) for p in listOfCityPops]
    # Computes population distribution statistics for the cities in the list, for end-of-game summary
    TOTAL_OVER_1M = sum(1 for p in all_city_pops if p > 1_000_000)
    TOTAL_OVER_500K = sum(1 for p in all_city_pops if p > 500_000)
    TOTAL_OVER_100K = sum(1 for p in all_city_pops if p > 100_000)
    TOTAL_OVER_50K = sum(1 for p in all_city_pops if p > 50_000)
except Exception:
    pop_max = 0
# Precompute canonical city names for case-insensitive and accent-insensitive matching (performance optimization)
listOfCityNamesCanonical = [
    canonical_city(name) for name in listOfCityNames
]
# Precompute population distribution statistics for end-of-game summary
def get_population_guess_stats():
    guessed_pops = [safe_int(p) for p in guessedCityPops]

    over_1m = sum(1 for p in guessed_pops if p > 1_000_000)
    over_500k = sum(1 for p in guessed_pops if p > 500_000)
    over_100k = sum(1 for p in guessed_pops if p > 100_000)
    over_50k = sum(1 for p in guessed_pops if p > 50_000)

    return over_1m, over_500k, over_100k, over_50k
# ---------------------------------
# O(1) dictionary lookups
# ---------------------------------
city_lookup = {}          # canonical city -> list of indices
city_state_lookup = {}    # (canonical city, state_abbrev) -> index
for i in range(len(listOfCityNames)):
    cname = listOfCityNamesCanonical[i]
    state = listOfCityStates[i].upper()
    # City-only lookup (may have multiple states)
    if cname not in city_lookup:
        city_lookup[cname] = []
    city_lookup[cname].append(i)
    # City + state lookup (unique)
    city_state_lookup[(cname, state)] = i
city_best_index_lookup = {}
for cname, indices in city_lookup.items():
    best_index = max(indices, key=lambda i: listOfCityPops[i])
    city_best_index_lookup[cname] = best_index
#open image file and read data
if state_lines_path.exists():
    try:
        img = mpimg.imread(state_lines_path)
        # show image in non-blocking mode so the driver loop continues
        plt.ion()
        # creates window sized to fit the image and leave space for the TextBox and guessed list
        fig, ax = plt.subplots(figsize=(18, 8))
        
        #show image on figure and set up a scatter artist for plotting guessed cities
        h, w = img.shape[0], img.shape[1]

        # Vertical divider line to separate the map from stats displayed on the right
        divider_x = 0.70
        divider = plt.Line2D(
            [divider_x, divider_x],  # x position
            [0, 1],                  # full height
            transform=fig.transFigure,
        color='black',
        linewidth=2
        )
        fig.add_artist(divider)
        # Add a header for the statistics panel on the right
        right_panel_center = 0.70 + (1.0 - 0.70) / 2  # center of right panel
        stats_header_artist = fig.text(
            right_panel_center,
            0.94,
            "Game Statistics",
            ha='center',
            va='center',
            fontsize=12,
            fontweight='bold',
            color='black'
        )
        #Largest 10 and Smallest 10 buttons
        largest_visible = False
        smallest_visible = False
        largest_button_x = 0.72
        largest_button_width = 0.12
        smallest_button_x = 0.86
        smallest_button_width = 0.12
        largest_center_x = largest_button_x + largest_button_width / 2
        smallest_center_x = smallest_button_x + smallest_button_width / 2
        # Best States Buttons
        btn_expand_ax = fig.add_axes([0.79, 0.585, 0.12, 0.035])
        btn_expand = Button(btn_expand_ax, "Expand States List")
        def toggle_expand(event):
            global best_states_expanded, best_states_scroll
            best_states_expanded = not best_states_expanded
            best_states_scroll = 0
            btn_expand.label.set_text("Collapse States List" if best_states_expanded else "Expand States List")
            update_best_states()
            fig.canvas.draw_idle()
        btn_expand.on_clicked(toggle_expand)
        # Largest 10 list (centered)
        top10_largest_artist = fig.text(
            largest_center_x,
            0.83,
            "",
            ha='center',
            va='top',
            fontsize=NEW_FONT_LIST,
            color='white',
            bbox=dict(facecolor='black', alpha=0.6, pad=5)
        )
        # Smallest 10 list (centered)
        smallest10_artist = fig.text(
            smallest_center_x,
            0.83,
            "",
            ha='center',
            va='top',
            fontsize=NEW_FONT_LIST,
            color='white',
            bbox=dict(facecolor='black', alpha=0.6, pad=5)
        )
        # Best States Panel
        best_states_center = 0.70 + (1.0 - 0.70) / 2
        best_states_artist = fig.text(
            best_states_center,
            0.55,
            "",
            ha='center',
            va='top',
            fontsize=NEW_FONT_LIST,
            color='white',
            bbox=dict(facecolor='black', alpha=0.6, pad=5)
        )
        population_stats_artist = fig.text(
            right_panel_center,   # already computed earlier
            0.08,                 # bottom area of right panel
            "",
            ha='center',
            va='bottom',
            fontsize=10,
            color='white',
            bbox=dict(facecolor='black', alpha=0.6, pad=5)
        )
        top10_largest_artist.set_visible(False)
        smallest10_artist.set_visible(False)
        # Image display
        ax.imshow(img, origin='upper')
        ax.set_xlim(0, w)
        ax.set_ylim(h, 0)
        ax.set_aspect('equal')   # VERY important
        ax.axis('off')
        ax.set_position([0.05, 0.1, 0.6, 0.8])
        # Store original axis limits for reset
        original_xlim = ax.get_xlim()
        original_ylim = ax.get_ylim()
        scatter_artist = ax.scatter([], [], c='red', edgecolors='black', alpha=0.5, zorder=6)
        try:
            fig.canvas.manager.set_window_title("State Lines")
        except Exception:
            pass
        plt.show(block=False)
        plt.pause(0.1)  # give the GUI event loop a moment to render the window

        # --- build an affine mapping from (lat, lon) -> (x_pixel, y_pixel)
        # Calibration points (lat, lon) -> (x_pixel, y_pixel)
        _cal_points = [
            (-29.472222, 129.271111, 15,   174),
            (-25.726944, 139.033889, 413,  11),
            (-44.853056, 143.34,     590,  900),
            (-35.277778, 163.403611, 1408, 440),
            (-37.5000170, 158.0684032, 1191, 543),
            (-34.5518073, 152.2154898, 952, 406),
            (-40.0017210, 141.7237776, 524, 662),
            (-30.5422765, 136.9500000, 328, 223),
        ]
        try:
            # Second-order polynomial transform:
            # x = a1*lon + a2*lat + a3*lon*lat + a4*lon^2 + a5*lat^2 + a6
            # y = same structure

            A = []
            Bx = []
            By = []

            for lat, lon, px, py in _cal_points:
                A.append([
                    lon,
                    lat,
                    lon*lat,
                    lon*lon,
                    lat*lat,
                    1
                ])
                Bx.append(px)
                By.append(py)

            A = np.array(A)
            Bx = np.array(Bx)
            By = np.array(By)

            params_x, *_ = np.linalg.lstsq(A, Bx, rcond=None)
            params_y, *_ = np.linalg.lstsq(A, By, rcond=None)

            def latlon_to_xy(lat, lon):
                vec = np.array([
                    lon,
                    lat,
                    lon*lat,
                    lon*lon,
                    lat*lat,
                    1
                ])
                x = np.dot(params_x, vec)
                y = np.dot(params_y, vec)
                return float(x), float(y)

            _has_geo_transform = True
        except Exception:
            _has_geo_transform = False
            def latlon_to_xy(lat, lon):
                raise RuntimeError("Geo transform not available")
    except Exception as e:
        print(f"Unable to open image {state_lines_path}: {e}", file=sys.stderr)
else:
    print(f"Image not found: {state_lines_path}", file=sys.stderr)

# prepare an on-image prompt (if the figure exists)
text_artist = None
if 'fig' in globals() and 'ax' in globals():
    prompt_text = "Enter the name of a city. Enter 'finish' to end the game:"
    # DO NOT create the prompt here (we'll create it under the TextBox after the TextBox axes are added)
    # create a figure-level text area centered above the TextBox to list guessed cities
    map_center = 0.05 + 0.6/2  # = 0.35
    guessed_list_artist = fig.text(
        map_center, 0.115, "", ha='center', va='top',
        fontsize=10, color='white',
        bbox=dict(facecolor='black', alpha=0.6, pad=5)
    )

    try:
        fig.canvas.draw_idle()
    except Exception:
        pass

if text_artist is not None:
    text_artist.set_fontsize(NEW_FONT_PROMPT)
if guessed_list_artist is not None:
    guessed_list_artist.set_fontsize(NEW_FONT_LIST)
"""Driver code to run the game.
This sets up the TextBox for user input on the image (if the figure was successfully loaded)
and then enters a loop prompting the user for city names until they enter 'finish'.
The on_submit callback handles the logic for processing user input and updating the game state."""
# Create on-image UI if figure exists; otherwise fall back to terminal loop
if 'fig' in globals() and 'ax' in globals():

    # textbox centered over map (map center = 0.35)
    map_center = 0.05 + 0.6/2  # = 0.35

    input_ax = fig.add_axes([map_center - 0.15, 0.92, 0.30, 0.04])
    text_box = TextBox(input_ax, '')
    # Recent guesses (top-right of TextBox)
    recent_guesses_artist = fig.text(
        map_center + 0.20, 0.94, "",   # move right of textbox
        ha='left', va='top',
        fontsize=NEW_FONT_LIST,
        color='white',
        bbox=dict(facecolor='black', alpha=0.6, pad=5)
    )
    # Ensure the on-image prompt and guessed-list text are placed at the BOTTOM
    # (only create them if not already created earlier to avoid duplicates)
    if text_artist is None:
        text_artist = fig.text(
            map_center, 0.885, prompt_text, ha='center', va='center',
            fontsize=NEW_FONT_PROMPT, color='white',
            bbox=dict(facecolor='black', alpha=0.6)
        )

    if guessed_list_artist is None:
        # move guessed list slightly up so it sits above the bottom prompt
        guessed_list_artist = fig.text(
            map_center, 0.5, "", ha='center', va='top',
            fontsize=10, color='white',
            bbox=dict(facecolor='black', alpha=0.6, pad=5)
        )

    # Move the up/down arrow buttons to sit next to the guessed list
    # left button to the left of the guessed list, right button to the right
    arrow_y = 0.01   # lower than before
    arrow_width = 0.055
    arrow_height = 0.05

    btn_up_ax = fig.add_axes([map_center - 0.12, arrow_y, arrow_width, arrow_height])
    btn_down_ax = fig.add_axes([map_center + 0.065, arrow_y, arrow_width, arrow_height])
    btn_up = Button(btn_up_ax, '↑', hovercolor='0.95')
    btn_down = Button(btn_down_ax, '↓', hovercolor='0.95')

    # Reset zoom button
    btn_reset_ax = fig.add_axes([map_center - 0.25, 0.92, 0.08, 0.04])
    btn_reset = Button(btn_reset_ax, 'Reset Zoom', hovercolor='0.95')

    def on_scroll_event(event):
        global guessed_scroll_start, best_states_scroll

        # If scroll is over the image axes → zoom
        if event.inaxes == ax:
            base_scale = 1.2

            if hasattr(event, "step"):
                direction = event.step
            elif hasattr(event, "button"):
                direction = 1 if event.button == 'up' else -1
            else:
                return

            if direction > 0:
                scale_factor = 1 / base_scale  # zoom in
            else:
                scale_factor = base_scale      # zoom out

            cur_xlim = ax.get_xlim()
            cur_ylim = ax.get_ylim()

            xdata = event.xdata
            ydata = event.ydata

            if xdata is None or ydata is None:
                return

            new_width = (cur_xlim[1] - cur_xlim[0]) * scale_factor
            new_height = (cur_ylim[1] - cur_ylim[0]) * scale_factor

            relx = (cur_xlim[1] - xdata) / (cur_xlim[1] - cur_xlim[0])
            rely = (cur_ylim[1] - ydata) / (cur_ylim[1] - cur_ylim[0])

            ax.set_xlim([xdata - new_width * (1 - relx),
                     xdata + new_width * relx])
            ax.set_ylim([ydata - new_height * (1 - rely),
                     ydata + new_height * rely])

        # Otherwise → scroll guessed list
        else:
            step = None
            if hasattr(event, "step"):
                step = -event.step
            elif hasattr(event, "button"):
                if event.button == 'up':
                    step = -1
                elif event.button == 'down':
                    step = 1

            if step is None:
                return

            guessed_scroll_start = max(0, guessed_scroll_start + step)
            update_guessed_list()

        # Scroll Best States if expanded and cursor is in right panel
        if best_states_expanded and event.x > fig.bbox.width * 0.70:

            if hasattr(event, "step"):
                step = -event.step
            elif hasattr(event, "button"):
                if event.button == 'up':
                    step = -1
                elif event.button == 'down':
                    step = 1
                else:
                    return
            else:
                return

            total_states = min(20, len(state_guess_counter))
            max_scroll = max(0, total_states - best_states_items_per_page)

            best_states_scroll = min(
                max(0, best_states_scroll + step),
                max_scroll
            )

            update_best_states()
            fig.canvas.draw_idle()
            return
    fig.canvas.draw_idle()
    
    def on_mouse_press(event):
        global is_panning, pan_start, pan_xlim, pan_ylim

        if event.inaxes != ax:
            return

        if event.button != 1:  # Left mouse button only
            return

        is_panning = True
        pan_start = (event.xdata, event.ydata)
        pan_xlim = ax.get_xlim()
        pan_ylim = ax.get_ylim()


    def on_mouse_release(event):
        global is_panning
        is_panning = False


    def on_mouse_move(event):
        global is_panning, pan_start

        if not is_panning:
            return

        if event.inaxes != ax:
            return

        if event.xdata is None or event.ydata is None:
            return

        dx = event.xdata - pan_start[0]
        dy = event.ydata - pan_start[1]

        cur_xlim = ax.get_xlim()
        cur_ylim = ax.get_ylim()

        ax.set_xlim(cur_xlim[0] - dx, cur_xlim[1] - dx)
        ax.set_ylim(cur_ylim[0] - dy, cur_ylim[1] - dy)

        # Update pan_start to current position (incremental update)
        pan_start = (event.xdata, event.ydata)

        # THROTTLED DRAW (Fix #3): Only redraw the figure at most every 0.02 seconds during panning to improve performance and reduce lag.
        if not hasattr(on_mouse_move, "last_draw_time"):
            on_mouse_move.last_draw_time = 0
        now = time.time()
        # Only redraw every 0.02 seconds (~50 FPS max)
        if now - on_mouse_move.last_draw_time > 0.02:
            fig.canvas.draw_idle()
            on_mouse_move.last_draw_time = now

    def on_up_clicked(event):
        global guessed_scroll_start
        guessed_scroll_start = max(0, guessed_scroll_start - items_per_page)
        update_guessed_list()

    def on_down_clicked(event):
        global guessed_scroll_start
        guessed_scroll_start = guessed_scroll_start + items_per_page
        update_guessed_list()

    def reset_zoom(event):
        ax.set_xlim(original_xlim)
        ax.set_ylim(original_ylim)
        fig.canvas.draw_idle()

    btn_up.on_clicked(on_up_clicked)
    btn_down.on_clicked(on_down_clicked)
    btn_reset.on_clicked(reset_zoom)

    btn_largest_ax = fig.add_axes([0.72, 0.88, 0.12, 0.035])
    btn_largest = Button(btn_largest_ax, "Show Largest Guesses")

    def toggle_largest(event):
        global largest_visible
        largest_visible = not largest_visible
        top10_largest_artist.set_visible(largest_visible)
        if largest_visible:
            btn_largest.label.set_text("Hide Largest Guesses")
            update_top10_largest_guessed()
        else:
            btn_largest.label.set_text("Show Largest Guesses")
        fig.canvas.draw_idle()

    btn_largest.on_clicked(toggle_largest)

    # Smallest toggle button
    btn_smallest_ax = fig.add_axes([0.86, 0.88, 0.12, 0.035])
    btn_smallest = Button(btn_smallest_ax, "Show Smallest Guesses")

    def toggle_smallest(event):
        global smallest_visible
        smallest_visible = not smallest_visible
        smallest10_artist.set_visible(smallest_visible)
        if smallest_visible:
            btn_smallest.label.set_text("Hide Smallest Guesses")
            update_smallest10_guessed()
        else:
            btn_smallest.label.set_text("Show Smallest Guesses")
        fig.canvas.draw_idle()

    btn_smallest.on_clicked(toggle_smallest)

    try:
        fig.canvas.mpl_connect('scroll_event', on_scroll_event)
        fig.canvas.mpl_connect('button_press_event', on_mouse_press)
        fig.canvas.mpl_connect('button_release_event', on_mouse_release)
        fig.canvas.mpl_connect('motion_notify_event', on_mouse_move)
    except Exception:
        pass

    # wire the TextBox submit callback (existing on_submit function)
    cid_submit = text_box.on_submit(on_submit)

    # initial render and single prompt display (prompt lives at bottom now)
    update_guessed_list()
    plt.draw()
    plt.pause(0.1)
    show_message("Enter the name of a city. Enter 'finish' to end the game:")
    # Hover tooltip setup (only create the tooltip annotation if not already created to avoid duplicates)
    if 'tooltip' not in globals():
        tooltip = ax.annotate(
            "", xy=(0,0), xytext=(10,10), textcoords="offset points",
            bbox=dict(boxstyle="round", fc="w"),
            arrowprops=dict(arrowstyle="->"),
            zorder=100  # Ensure tooltip always appears on top
        )
        tooltip.set_visible(False)

    def on_hover(event):
        if event.inaxes != ax:
            if tooltip.get_visible():
                tooltip.set_visible(False)
                fig.canvas.draw_idle()
            return
        if not scatter_x:
            return

        contains, info = scatter_artist.contains(event)

        if contains:
            ind = info["ind"][0]
            city_name = guessedCityNames[ind]
            state_abbr = guessedCityStates[ind]
            state_display = stateAbbreviations.get(state_abbr, state_abbr)
            pop = guessedCityPops[ind]
            tooltip.set_text(f"{city_name}, {state_display}: {pop:,}")
            tooltip.xy = (scatter_x[ind], scatter_y[ind])
            if not tooltip.get_visible():
                tooltip.set_visible(True)
                fig.canvas.draw_idle()
        else:
            if tooltip.get_visible():
                tooltip.set_visible(False)
                fig.canvas.draw_idle()

    # connect the hover event
    if 'hover_cid' not in globals():
        hover_cid = fig.canvas.mpl_connect("motion_notify_event", on_hover)
else:
    # Fallback: no figure available, keep the terminal prompt-driven loop (uses prompt_city)
    print("No figure available for hover events.")
    
# Start GUI event loop
plt.show(block=True)
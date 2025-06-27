# -*- coding: utf-8 -*-
"""
Created on Mon May 19 09:39:38 2025

@author: Admin
"""
from IPython import get_ipython
ipython = get_ipython()
if ipython:
    ipython.run_line_magic('reset', '-sf')

import folium
import pandas as pd
import geopandas as gpd
from shapely.geometry import Point, Polygon
from shapely.validation import make_valid
from shapely.ops import polylabel
import re
from datetime import datetime, timedelta
import math
import requests
import xml.etree.ElementTree as ET
import traceback
from bs4 import BeautifulSoup
import time

region_order_map = {
    "NCR (National Capital Region)": 0,
    "Region 1 (Ilocos Region)": 1,
    "CAR (Cordillera Administrative Region)": 2,
    "Region 2 (Cagayan Valley)": 3,
    "Region 3 (Central Luzon)": 4,
    "Region 4-A (CALABARZON)": 5,
    "Region 4-B (MIMAROPA)": 6,
    "Region 5 (Bicol Region)": 7,
    "Region 6 (Western Visayas)": 8,
    "Region 7 (Central Visayas)": 9,
    "Region 8 (Eastern Visayas)": 10,
    "Region 9 (Zamboanga Peninsula)": 11,
    "Region 10 (Northern Mindanao)": 12,
    "Region 11 (Davao Region)": 13,
    "Region 12 (SOCCSKSARGEN)": 14,
    "Region 13 (Caraga)": 15,
    "BARMM (Bangsamoro Autonomous Region in Muslim Mindanao)": 16,
    "N/A Region": 999
}

def format_issued_time(sent_str):
    try:
        sent_dt = datetime.fromisoformat(sent_str.replace('Z', '+00:00'))
    except ValueError:
        return f"N/A, {datetime.now().strftime('%d %B %Y')}", ""

    morning_start = sent_dt.replace(hour=4, minute=0, second=0, microsecond=0)
    morning_end = sent_dt.replace(hour=7, minute=0, second=0, microsecond=0)
    evening_start = sent_dt.replace(hour=16, minute=0, second=0, microsecond=0)
    evening_end = sent_dt.replace(hour=19, minute=0, second=0, microsecond=0)

    display_time_str = ""
    validity_info = ""

    if morning_start <= sent_dt <= morning_end:
        display_time_str = "6:00 am"
        validity_info = "Valid until the next issuance at 6:00 pm today"
    elif evening_start <= sent_dt <= evening_end:
        display_time_str = "6:00 pm"
        validity_info = "Valid until the next issuance at 6:00 am tomorrow"
    else:
        time_to_round = sent_dt.replace(second=0, microsecond=0)
        total_minutes_since_midnight = time_to_round.hour * 60 + time_to_round.minute

        if total_minutes_since_midnight % 30 == 0:
            rounded_total_minutes = total_minutes_since_midnight
        else:
            rounded_total_minutes = math.ceil(total_minutes_since_midnight / 30) * 30

        start_of_day_sent = sent_dt.replace(hour=0, minute=0, second=0, microsecond=0)
        rounded_dt_for_display = start_of_day_sent + timedelta(minutes=rounded_total_minutes)
        display_time_str = rounded_dt_for_display.strftime("%I:%M %p").lower().replace('am', 'am').replace('pm', 'pm')

        if sent_dt.hour < 6:
            validity_info = "Valid until the next issuance at 6:00 am tomorrow"
        elif sent_dt.hour < 18:
            validity_info = "Valid until the next issuance at 6:00 pm today"
        else:
            validity_info = "Valid until the next issuance at 6:00 am tomorrow"

    date_part = sent_dt.strftime("%d %B %Y")

    return f"{display_time_str}, {date_part}", validity_info

def get_styled_province_function(province_info_dict):
    def styled_province_function(feature):
        province_name_from_geojson = feature['properties'].get('adm2_en')

        if isinstance(province_name_from_geojson, str):
            cleaned_province_name_geojson_lower = province_name_from_geojson.replace('Province of ', '').strip().lower()
        else:
            cleaned_province_name_geojson_lower = None

        info = province_info_dict.get(cleaned_province_name_geojson_lower, {'color': 'white', 'severity_level': 0})
        fill_color = info['color']
        fill_opacity = 0.9 if fill_color != 'white' else 0
        weight = 0.6 if fill_color != 'white' else 0.1

        return {
            'fillColor': fill_color,
            'color': 'black',
            'weight': weight,
            'fillOpacity': fill_opacity,
        }
    return styled_province_function

def process_instruction_text(instruction_text):
    if not isinstance(instruction_text, str):
        return instruction_text
    
    modified_text_step1 = instruction_text

    instruction_lower = instruction_text.lower()
    if "flashfloods" in instruction_lower and "landslides" not in instruction_lower:
        modified_text_step1 = re.sub(
            r'flashfloods',
            r'flashfloods and landslides',
            instruction_text,
            count=1,
            flags=re.IGNORECASE
        )

    modified_text_step2 = modified_text_step1.strip()
    modified_text_step2 = modified_text_step2.rstrip('.')
    modified_text_step2 += '.'

    return modified_text_step2

def generate_tooltip_html(feature, province_info_dict):
    province_name_from_geojson = feature['properties'].get('adm2_en')
    if isinstance(province_name_from_geojson, str):
        cleaned_province_name_geojson_lower = province_name_from_geojson.replace('Province of ', '').strip().lower()
    else:
        cleaned_province_name_geojson_lower = None

    info = province_info_dict.get(cleaned_province_name_geojson_lower, {
        'color': 'white',
        'severity_level': 0,
        'event': 'No Advisory',
        'identifier': 'N/A',
        'region': 'N/A',
        'sent': 'N/A',
        'instruction': 'No specific instructions.',
        'rivers_info': 'N/A',
        'present_weather': 'N/A',
        'rainfall_forecast': 'N/A'
    })

    original_event = info['event']
    display_event_text = original_event

    if 'moderate' in original_event.lower():
        display_event_text = 'Flood Monitoring'
    elif 'severe' in original_event.lower():
        display_event_text = 'Flood Alert'
    elif 'extreme' in original_event.lower():
        display_event_text = 'Flood Warning'
    elif 'final' in original_event.lower():
        display_event_text = 'Final'

    background_color_code = info['color']
    text_color_code = 'black'
    if background_color_code in ['#B22B42', '#E6793B', '#777777']:
        text_color_code = 'white'

    event_status_style = f"background-color: {background_color_code}; color: {text_color_code}; padding: 2px 5px; border-radius: 3px; font-weight: bold;"

    html_content = ""

    if info['region'] != 'N/A':
        html_content += f"""
    <strong>Region:</strong> {info['region']}<br>
        """

    html_content += f"""
    <strong>Province:</strong> {province_name_from_geojson or 'N/A'}<br>
    <strong>General Flood Advisory:</strong> <span style="{event_status_style}">{display_event_text}</span>
    """

    if display_event_text == 'Final':
        html_content += f"""
            <div style="white-space: normal; word-wrap: break-word; overflow-wrap: break-word; max-width: 100%;"><br>Flood is no longer likely unless significant rain occurs.</div>
            """

    if info['severity_level'] > 0:
        instruction_text = info.get('instruction', 'No specific instructions.')
        if not instruction_text.strip():
            instruction_text = 'No specific instructions.'

        instruction_text = instruction_text.replace('**', '')
        modified_instruction_text = re.sub(r'(concerned)(?!\w)', r'\1 are', instruction_text, flags=re.IGNORECASE, count=1)
        modified_instruction_text = re.sub(r'(near)\s+the\s+(mountain slopes)', r'\1 \2', modified_instruction_text, flags=re.IGNORECASE)
        modified_instruction_text = re.sub(r'(in)\s+the\s+(low lying areas)', r'\1 \2', modified_instruction_text, flags=re.IGNORECASE)
        final_instruction_text = modified_instruction_text

        phrases_to_underline = [
            r"near mountain slopes",
            r"in low lying areas"
        ]
        for phrase_pattern in phrases_to_underline:
            final_instruction_text = re.sub(
                r'(' + phrase_pattern + r')',
                r'<u>\1</u>',
                final_instruction_text,
                flags=re.IGNORECASE
            )

        idx_to = final_instruction_text.lower().find("to")

        if idx_to != -1:
            part_before_to = final_instruction_text[:idx_to]

            len_to = len("to")

            part_to_format = final_instruction_text[idx_to + len_to:]

            trailing_period = ''
            if part_to_format.endswith('.'):
                trailing_period = '.'
                part_to_format = part_to_format[:-1]

            instruction_style = "font-weight: bold; text-decoration: underline;"

            final_instruction_text = (
                part_before_to +
                "to " +
                f"<span style='{instruction_style}'>{part_to_format}</span>" +
                trailing_period
            )

        instruction_html_content = f'<div style="white-space: normal; word-wrap: break-word; overflow-wrap: break-word; max-width: 100%;">{final_instruction_text}</div>'

        issued_date_time, validity_period = format_issued_time(info['sent'])

        html_content += f"""<br>
    <strong>Issued at:</strong> {issued_date_time}<br>
    {validity_period}<br>
        """

        present_weather = info.get('present_weather')
        if present_weather and present_weather != 'N/A':
            html_content += f"""<br>
    <strong>Present weather:</strong> <div style="white-space: normal; word-wrap: break-word; overflow-wrap: break-word; max_width: 100%;">{present_weather}</div>
            """

        rainfall_forecast = info.get('rainfall_forecast')
        if rainfall_forecast and rainfall_forecast != 'N/A':
            html_content += f"""
    <strong>Forecast 12-hour rainfall:</strong> <div style="white-space: normal; word-wrap: break-word; overflow-wrap: break-word; max_width: 100%;">{rainfall_forecast}</div>
            """

        rivers_info = info.get('rivers_info')
        if rivers_info and rivers_info != 'N/A':
            html_content += f"""
    <strong>Watercourses likely to be affected:</strong> <div style="white-space: normal; word-wrap: break-word; overflow-wrap: break-word; max_width: 100%;">{rivers_info}</div>
            """

        html_content += f"""<br>
    <strong>Instruction:</strong> {instruction_html_content}
        """
    return html_content

def extract_gfa_identifiers(target_date_str: str, am_pm_str: str):
    target_url = "https://publicalert.pagasa.dost.gov.ph/output/gfa/?C=M;O=D"
    matching_identifiers = []

    try:
        target_date_obj = datetime.strptime(target_date_str, '%Y-%m-%d').date()
    except ValueError:
        print(f"Error: Invalid date format '{target_date_str}'. Please use YYYY-MM-DD.")
        return []

    start_hour = 0
    end_hour = 0

    if am_pm_str.lower() == 'am':
        start_hour = 0
        end_hour = 11
        print(f"Searching for advisories on {target_date_str} (am: 00:00 - 11:59)...")
    elif am_pm_str.lower() == 'pm':
        start_hour = 12
        end_hour = 23
        print(f"Searching for advisories on {target_date_str} (pm: 12:00 - 23:59)...")
    else:
        print(f"Error: Invalid AM/PM input '{am_pm_str}'. Please use 'am' or 'pm'.")
        return []

    print(f"Attempting to extract GFA identifiers from: {target_url}...")
    try:
        response = requests.get(target_url, timeout=10)
        response.raise_for_status()

        soup = BeautifulSoup(response.content, 'html.parser')
        
        cap_links = soup.find_all('a', href=re.compile(r'^(?!.*\.\./).*(\.cap)$'))

        for link in cap_links:
            href = link.get('href')
            identifier = href.replace('.cap', '')

            if not re.fullmatch(r'[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}', identifier):
                continue

            parent_td = link.find_parent('td')
            if parent_td:
                parent_tr = parent_td.find_parent('tr')
                if parent_tr:
                    tds = parent_tr.find_all('td')
                    if len(tds) > 2:
                        time_str_raw = tds[2].get_text(strip=True)
                        try:
                            modification_time = datetime.strptime(time_str_raw, '%d-%b-%Y %H:%M')
                            if modification_time.date() < target_date_obj:
                                print(f"Encountered an advisory older than {target_date_obj}. Stopping search early.")
                                break

                            if (modification_time.date() == target_date_obj and
                                start_hour <= modification_time.hour <= end_hour):
                                matching_identifiers.append(identifier)

                        except ValueError:
                            print(f"Warning: Could not parse date/time '{time_str_raw}' for identifier {identifier}. Skipping.")
                            continue
    
    except requests.exceptions.RequestException as e:
        print(f"Error fetching URL ({target_url}): {e}")
        return []
    except Exception as e:
        print(f"An error occurred during HTML parsing ({target_url}): {e}")
        traceback.print_exc()
        return []

    if not matching_identifiers:
        print(f"No CAP identifiers found for {target_date_str} {am_pm_str.lower()} with valid timestamps.")
        return []

    print(f"Found {len(matching_identifiers)} identifiers for {target_date_str} {am_pm_str.lower()}.")
    return matching_identifiers

def extract_cap_data(identifier):
    cap_url = f"https://publicalert.pagasa.dost.gov.ph/output/gfa/{identifier}.cap"
    cap_data = {}
    area_descriptions = []
    region_value = 'N/A'
    event_value = 'N/A'
    instruction_value = 'No specific instructions.'
    description_value = 'N/A'
    present_weather_value = 'N/A'
    rainfall_forecast_value = 'N/A'
    severity_raw_value = 'Unknown'
    msg_type_value = 'N/A'
    references_value = None

    try:
        response = requests.get(cap_url)
        response.raise_for_status()

        root = ET.fromstring(response.content)

        namespaces = {
            'cap': 'urn:oasis:names:tc:emergency:cap:1.2',
        }

        sent_element = root.find('cap:sent', namespaces)
        msg_type_element = root.find('cap:msgType', namespaces)
        references_element = root.find('cap:references', namespaces)
        info_element = root.find('cap:info', namespaces)

        event_element = info_element.find('cap:event', namespaces) if info_element is not None else None
        if event_element is not None and event_element.text is not None:
            event_value = event_element.text.strip()

        severity_element = info_element.find('cap:severity', namespaces) if info_element is not None else None
        severity_raw_value = severity_element.text.strip() if severity_element is not None and severity_element.text is not None else 'Unknown'

        area_elements = info_element.findall('cap:area', namespaces) if info_element is not None else []
        for area_element in area_elements:
            area_desc_element = area_element.find('cap:areaDesc', namespaces)
            if area_desc_element is not None and area_desc_element.text is not None:
                area_descriptions.append(area_desc_element.text.strip())

        instruction_element = info_element.find('cap:instruction', namespaces) if info_element is not None else None
        if instruction_element is not None and instruction_element.text is not None:
            instruction_value = instruction_element.text.strip()
            instruction_value = process_instruction_text(instruction_value)

        description_element = info_element.find('cap:description', namespaces) if info_element is not None else None
        if description_element is not None and description_element.text is not None:
            description_value = description_element.text.strip()
            description_value = process_instruction_text(description_value)

            present_weather_match = re.search(r"Under present weather conditions,(.*?)\s*The 12-hour rainfall forecast is", description_value, re.DOTALL)
            if present_weather_match:
                present_weather_value = present_weather_match.group(1).strip()

            rainfall_forecast_match = re.search(r"The 12-hour rainfall forecast is(.*?)(?:\s*WATERCOURSES (?:STILL )?LIKELY TO BE AFFECTED :|\s*$)", description_value, re.DOTALL)
            if rainfall_forecast_match:
                rainfall_forecast_value = rainfall_forecast_match.group(1).strip()

                if rainfall_forecast_value:
                    rainfall_forecast_value = rainfall_forecast_value[0].upper() + rainfall_forecast_value[1:].lower()


        parameter_elements = info_element.findall('cap:parameter', namespaces) if info_element is not None else []
        for param_element in parameter_elements:
            value_name_element = param_element.find('cap:valueName', namespaces)
            value_element = param_element.find('cap:value', namespaces)

            if value_name_element is not None and value_name_element.text is not None and \
               value_name_element.text.strip() == 'layer:Google:Region:0.1' and \
               value_element is not None and value_element.text is not None:
                region_value = value_element.text.strip()
                break

        cap_data['sent'] = sent_element.text.strip() if sent_element is not None and sent_element.text is not None else 'N/A'
        cap_data['event'] = event_value
        cap_data['areaDescs'] = area_descriptions
        cap_data['region'] = region_value
        cap_data['instruction'] = instruction_value
        cap_data['description'] = description_value
        cap_data['present_weather'] = present_weather_value
        cap_data['rainfall_forecast'] = rainfall_forecast_value
        cap_data['rivers_info_by_province'] = {}
        cap_data['severity_raw'] = severity_raw_value
        cap_data['msgType'] = msg_type_element.text.strip() if msg_type_element is not None and msg_type_element.text is not None else 'N/A'
        cap_data['references'] = references_element.text.strip() if references_element is not None and references_element.text is not None else None

        if region_value == "Region 11 (Davao Region)":
            davao_occidental_pattern = r"\+\s*\*\*Davao Occidental\*\*"
            if re.search(davao_occidental_pattern, description_value, re.DOTALL):
                if "Davao Occidental" not in area_descriptions:
                    area_descriptions.append("Davao Occidental")

        text_to_parse_watercourses = None

        watercourses_pattern = r"WATERCOURSES (?:STILL )?LIKELY TO BE AFFECTED :"

        if instruction_value and re.search(watercourses_pattern, instruction_value):
            text_to_parse_watercourses = instruction_value
        elif description_value and re.search(watercourses_pattern, description_value):
            text_to_parse_watercourses = description_value

        if text_to_parse_watercourses:
            match = re.search(watercourses_pattern, text_to_parse_watercourses)
            if match:
                start_index = match.end()
                watercourses_text = text_to_parse_watercourses[start_index:].strip()

                pattern_findall = r'\+\s*\*\*(.*?)\*\*\s*-\s*(.*?)(?=\s*\+\s*\*\*|\s*$)'
                matches = re.findall(pattern_findall, watercourses_text)

                for province_name_raw, rivers_description_raw in matches:
                    cleaned_province_name = province_name_raw.replace('Province of ', '').strip().lower()

                    cleaned_rivers_description = rivers_description_raw.replace('\xa0', ' ').strip()

                    cap_data['rivers_info_by_province'][cleaned_province_name] = cleaned_rivers_description

    except requests.exceptions.RequestException as e:
        print(f"Error fetching CAP file for identifier {identifier}: {e}")
        return None
    except ET.ParseError as e:
        print(f"Error parsing CAP file for identifier {identifier}: {e}")
        return None
    except Exception as e:
        print(f"An unexpected error occurred for identifier {identifier}: {e}")
        traceback.print_exc()
        return None

    cap_data['areaDescs'] = area_descriptions
    return cap_data

def filter_active_advisories(all_raw_gfa_data: dict) -> dict:
    cancelled_or_superseded_ids = set()
    
    for identifier, cap_data in all_raw_gfa_data.items():
        msg_type = cap_data.get('msgType')
        references_str = cap_data.get('references')
            
        if msg_type == 'Cancel':
            cancelled_or_superseded_ids.add(identifier)
            if references_str:
                parts = references_str.split(',')
                if len(parts) >= 2:
                    referred_id = parts[1].strip()
                    if re.fullmatch(r'[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}', referred_id):
                        cancelled_or_superseded_ids.add(referred_id)
                    else:
                        print(f"Warning: Invalid ID format in references for {identifier}: '{referred_id}'. Not adding to cancelled list.")
                else:
                    print(f"Warning: Malformed references string for {identifier}: '{references_str}'.")

        elif msg_type == 'Update':
            if references_str:
                parts = references_str.split(',')
                if len(parts) >= 2:
                    referred_id = parts[1].strip()
                    if re.fullmatch(r'[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}', referred_id):
                        cancelled_or_superseded_ids.add(referred_id)
                    else:
                        print(f"Warning: Invalid ID format in references for update {identifier}: '{referred_id}'. Not marking as superseded.")
                else:
                    print(f"Warning: Malformed references string for update {identifier}: '{references_str}'.")

    active_gfa_data = {}
    for identifier, cap_data in all_raw_gfa_data.items():
        if identifier not in cancelled_or_superseded_ids:
            active_gfa_data[identifier] = cap_data

    print(f"Identified {len(cancelled_or_superseded_ids)} CAP files (including cancellations and superseded advisories) to be excluded.")
    print(f"Remaining active advisories: {len(active_gfa_data)}")

    return active_gfa_data

def get_severity_color(severity_string):
    if severity_string:
        severity_string_lower = severity_string.lower()
        if 'extreme' in severity_string_lower:
            return '#B22B42'
        elif 'severe' in severity_string_lower:
            return '#E6793B'
        elif 'moderate' in severity_string_lower:
            return '#F3C218'
        elif 'minor' in severity_string_lower or 'unknown' in severity_string_lower or 'none' in severity_string_lower:
            return '#777777'
    return 'white'

def get_severity_level(severity_string):
    if severity_string:
        severity_string_lower = severity_string.lower() 
        if 'extreme' in severity_string_lower:
            return 3
        elif 'severe' in severity_string_lower:
            return 2
        elif 'moderate' in severity_string_lower:
            return 1
    return 0

provinces_by_gfa_type_for_summary = {}

gfa_category_order = [
    "Flood Warning",
    "Flood Alert",
    "Flood Monitoring",
    "Final Advisory"
]

def format_gfa_provinces(provinces_by_gfa_type, event_details, issued_date_time_part, validity_info_part):
    color_map = {
        "Flood Warning": {"background": "#B22B42", "text": "#FFFFFF"},
        "Flood Alert": {"background": "#E6793B", "text": "#FFFFFF"},
        "Flood Monitoring": {"background": "#F3C218", "text": "#000000"},
        "Final Advisory": {"background": "#777777", "text": "#FFFFFF"},
        # "No Advisory": {"background": "#DDDDDD", "text": "#333333"}
    }

    formatted_html = """
    """
    if not provinces_by_gfa_type:
         formatted_html += f"""
        <div style="font-size: 12px; margin-top: 8px; text-align: center; color: #555;">No provinces are currently under General Flood Advisory.</div>
        """
    else:
        for gfa_type in gfa_category_order:
            if gfa_type in provinces_by_gfa_type:
                provinces = provinces_by_gfa_type[gfa_type]
                colors = color_map.get(gfa_type, {"background": "#FFFFFF", "text": "#333333"})
                details = event_details.get(gfa_type, {'text': '', 'icon': ''})
                
                icon_html = f'<img src="{details["icon"]}" style="width: 36px; height: 36px; margin-right: 4px; flex-shrink: 0;">' if details['icon'] else ''

                formatted_html += f"""
                <div style="
                    font-size: 14px;
                    display: flex;
                    align-items: center;
                    width: 100%;
                    text-align: left;
                    margin-top: 8px;
                    padding: 4px 8px 5px 4px;
                    border-radius: 3px;
                    background-color: {colors['background']};
                    color: {colors['text']};
                    font-weight: bold;
                ">
                    {icon_html}
                    <div style="flex-grow: 1;">
                        {gfa_type}
                        <div style="font-size: 12px; font-weight: normal; line-height: 1.2;">{details['text']}</div>
                    </div>
                </div>
                <ul style='margin: 0; margin-top: 4px; padding-left: 20px; list-style-type: disc; list-style-position: outside; column-count: 2; column-gap: 8px; break-inside: avoid;'>
                """
                for province in provinces:
                    formatted_html += f"<li style='font-size: 12px; margin-bottom: 2px; color: #333;'>{province}</li>"
                formatted_html += "</ul>"
    return formatted_html

def create_flood_map(gfa_data, province_geojson_path):
    map_center = [12.8797, 121.7740]
    m = folium.Map(location=map_center, zoom_start=6, tiles=None)

    folium.TileLayer(
        tiles="Esri.WorldGrayCanvas",
        name="Basemap (ESRI World Gray Canvas)",
        control=True
    ).add_to(m)

    m.get_root().html.add_child(folium.Element("<title>General Flood Advisories | DOST-PAGASA</title>"))
    m.get_root().html.add_child(folium.Element(
        '<link rel="icon" href="https://pubfiles.pagasa.dost.gov.ph/pagasaweb/images/pagasa-logo.png" type="image/png">'
    ))

    southwest = (4, 116)
    northeast = (21.5, 127)

    province_info = {}
    for identifier, data in gfa_data.items():
        event = data.get('event', '')
        severity_raw = data.get('severity_raw', 'Unknown')
        severity_color = get_severity_color(severity_raw)
        severity_level = get_severity_level(severity_raw)
        
        area_descs = data.get('areaDescs', [])
        region = data.get('region', 'N/A')
        sent_time = data.get('sent', 'N/A')
        instruction = data.get('instruction', 'N/A')
        present_weather_data = data.get('present_weather', 'N/A')
        rainfall_forecast_data = data.get('rainfall_forecast', 'N/A')
        rivers_data_for_this_cap = data.get('rivers_info_by_province', {})

        for province_name_from_cap in area_descs:
            if isinstance(province_name_from_cap, str) and province_name_from_cap.strip():
                cleaned_province_name_cap_lower = province_name_from_cap.replace('Province of ', '').strip().lower()
                current_max_severity = province_info.get(cleaned_province_name_cap_lower, {}).get('severity_level', -1)

                if severity_level > current_max_severity:
                    province_rivers_info = rivers_data_for_this_cap.get(cleaned_province_name_cap_lower, 'N/A')
                    
                    province_info[cleaned_province_name_cap_lower] = {
                        'color': severity_color,
                        'severity_level': severity_level,
                        'event': event,
                        'identifier': identifier,
                        'region': region,
                        'sent': sent_time,
                        'instruction': instruction,
                        'present_weather': present_weather_data,
                        'rainfall_forecast': rainfall_forecast_data,
                        'rivers_info': province_rivers_info
                    }

    try:
        provinces_gdf = gpd.read_file(province_geojson_path)
    except FileNotFoundError:
        print(f"\nError: Province GeoJSON file not found at {province_geojson_path}")
        print("Please provide a valid path to a GeoJSON file containing Philippine province boundaries.")
        print("You can try searching online for 'Philippine provinces GeoJSON'.")
        return
    except Exception as e:
        print(f"\nError loading or processing GeoJSON file: {e}")
        traceback.print_exc()
        return

    event_details = {
        "Flood Warning": {
            'text': 'Take appropriate actions immediately.',
            'icon': 'https://pubfiles.pagasa.dost.gov.ph/pagasaweb/icons/hazard/flood/64/flood-warning.png'
        },
        "Flood Alert": {
            'text': 'Be alert for possible flashfloods and landslides.',
            'icon': 'https://pubfiles.pagasa.dost.gov.ph/pagasaweb/icons/hazard/flood/64/flood-alert.png'
        },
        "Flood Monitoring": {
            'text': 'Take necessary precautionary measures.',
            'icon': 'https://pubfiles.pagasa.dost.gov.ph/pagasaweb/icons/hazard/flood/64/flood-monitoring.png'
        },
        "Final Advisory": {
            'text': 'Flood is no longer likely unless significant rain occurs.',
            'icon': 'https://pubfiles.pagasa.dost.gov.ph/pagasaweb/icons/hazard/flood/64/final.png'
        },
        "No Advisory": {
            'text': 'No provinces are currently under General Flood Advisory.',
            'icon': ''
        }
    }

    provinces_by_gfa_type_for_summary = {}
    for cleaned_prov_name_lower, info in province_info.items():
        original_province_name = next((
            feature['properties']['adm2_en'] for feature in provinces_gdf.iterfeatures()
            if feature['properties'].get('adm2_en', '').replace('Province of ', '').strip().lower() == cleaned_prov_name_lower
        ), cleaned_prov_name_lower.title())

        province_region_name = info.get('region', 'N/A Region')
        province_region_sort_key = region_order_map.get(province_region_name, 999)

        display_summary_event_text = info['event']
        if 'moderate' in info['event'].lower():
            display_summary_event_text = 'Flood Monitoring'
        elif 'severe' in info['event'].lower():
            display_summary_event_text = 'Flood Alert'
        elif 'extreme' in info['event'].lower():
            display_summary_event_text = 'Flood Warning'
        elif 'final' in info['event'].lower():
            display_summary_event_text = 'Final Advisory'
        elif 'no advisory' in info['event'].lower():
            display_summary_event_text = 'No Advisory'

        if display_summary_event_text not in provinces_by_gfa_type_for_summary:
            provinces_by_gfa_type_for_summary[display_summary_event_text] = []
        provinces_by_gfa_type_for_summary[display_summary_event_text].append((province_region_sort_key, original_province_name))

    sorted_provinces_by_gfa_type = {}
    for gfa_type in gfa_category_order:
        if gfa_type in provinces_by_gfa_type_for_summary:
            provinces_for_gfa_type = provinces_by_gfa_type_for_summary[gfa_type]

            provinces_for_gfa_type.sort(key=lambda x: (x[0], x[1]))

            sorted_province_names_only = [prov_name for _, prov_name in provinces_for_gfa_type]
            sorted_provinces_by_gfa_type[gfa_type] = sorted_province_names_only

    issued_date_time_part = "N/A"
    validity_info_part = ""

    if gfa_data and any(gfa_data.values()):
        latest_sent_time = None
        for data in gfa_data.values():
            sent = data.get('sent')
            if sent != 'N/A':
                try:
                    current_sent_dt = datetime.strptime(sent, '%Y-%m-%dT%H:%M:%S%z')
                    if latest_sent_time is None or current_sent_dt > latest_sent_time:
                        latest_sent_time = current_sent_dt
                except ValueError:
                    pass
        if latest_sent_time:
            issued_date_time_part, validity_info_part = format_issued_time(latest_sent_time.isoformat())

    gfa_provinces_summary_text = format_gfa_provinces(sorted_provinces_by_gfa_type, event_details, issued_date_time_part, validity_info_part)

    info_html = f"""
    <div id="InfoBox" style="
        position: absolute;
        top: 10px;
        left: 10px;
        z-index: 1000;
        background-color: white;
        padding: 8px;
        border-radius: 4px;
        display: flex;
        flex-direction: column;
        align-items: flex-start;
        font-family: Arial, sans-serif;
        border: 2px solid rgba(0,0,0,0.35);
        width: 320px;
        max-width: 320px;
    ">
        <div style="display: flex; align-items: center; width: 100%; margin-bottom: 4px;">
            <img src="https://pubfiles.pagasa.dost.gov.ph/pagasaweb/images/pagasa-logo.png" alt="PAGASA Logo" style="width: 44px; height: 44px; margin-right: 8px;">
            <div style="display: flex; flex-direction: column;">
                <span style="font-size: 14px; font-weight: bold; color: #333;">DOST-PAGASA</span>
                <span style="font-size: 14px; color: #555;">Flood Forecasting and Warning Center</span>
            </div>
        </div>

        <div style="display: flex; flex-direction: column; width: 100%; border-bottom: 1px solid #eee; padding-bottom: 8px; margin-bottom: 8px;">
            <span style="font-size: 24px; font-weight: bold; color: #333; margin-top: 2px">General Flood Advisories</span>
            <span style="font-size: 14px; color: #333;">Issued at: {issued_date_time_part}</span>
            <span style="font-size: 11px; color: #333;">({validity_info_part})</span>
        </div>

        <div id="provincesHeader" style="
            font-size: 14px;
            font-weight: bold;
            cursor: pointer;
            color: #333;
            display: flex;
            justify-content: space-between;
            align-items: center;
            user-select: none;
            width: 100%;
        ">
            <span>Provinces under Active Advisories:</span>
            <i class="fa-solid fa-chevron-up" id="collapseIcon" style="transition: transform 0.3s ease-in-out;"></i>
        </div>
        <div id="provincesSummaryContent" style="
            font-size: 14px;
            max-height: calc(100vh - 197px);
            overflow-y: auto;
            box-sizing: border-box;
            width: 100%;
            display: block;
            transition: max-height 0.3s ease-in-out;
        ">
            {gfa_provinces_summary_text}
        </div>
        </div>
    """
    m.get_root().html.add_child(folium.Element(info_html))

    toggle_script = """
    <script>
        document.addEventListener('DOMContentLoaded', function() {
            var header = document.getElementById('provincesHeader');
            var content = document.getElementById('provincesSummaryContent');
            var icon = document.getElementById('collapseIcon');
            var infoBox = document.getElementById('InfoBox');

            var isThreeColumn = false;

            function adjustLayout() {
                if (!infoBox) {
                    console.warn("Info box element not found for width adjustment.");
                    return;
                }

                var provinceLists = content.querySelectorAll('ul');
                var provinceItems = content.querySelectorAll('li');

                if (content.scrollHeight > content.clientHeight && !isThreeColumn) {
                    provinceLists.forEach(function(ul) {
                        ul.style.columnCount = '3';
                        ul.style.columnGap = '8px';
                    });
                    provinceItems.forEach(function(li) {
                        li.style.fontSize = '11px';
                        li.style.marginBottom = '1px';
                    });
                    infoBox.style.width = '400px';
                    infoBox.style.maxWidth = '400px';
                    isThreeColumn = true;
                    console.log('Switched to 3 columns / 360px width / 11px font size due to scrollbar.');

                } else if (!isThreeColumn) {
                    provinceLists.forEach(function(ul) {
                        ul.style.columnCount = '2';
                        ul.style.columnGap = '8px';
                    });
                    provinceItems.forEach(function(li) {
                        li.style.fontSize = '12px';
                    });
                    infoBox.style.width = '320px';
                    infoBox.style.maxWidth = '320px';
                    console.log('Reverted to 2 columns / 320px width / 12px font size (no scrollbar).');
                }
            }

            content.style.display = 'block';
            icon.classList.remove('fa-chevron-down');
            icon.classList.add('fa-chevron-up');

            adjustLayout();

            header.onclick = function() {
                if (content.style.display === 'none' || content.style.display === '') {
                    content.style.display = 'block';
                    icon.classList.remove('fa-chevron-down');
                    icon.classList.add('fa-chevron-up');
                    adjustLayout();
                } else {
                    content.style.display = 'none';
                    icon.classList.remove('fa-chevron-up');
                    icon.classList.add('fa-chevron-down');
                }
            };

            window.addEventListener('resize', adjustLayout);
        });
    </script>
    """
    m.get_root().html.add_child(folium.Element(toggle_script))

    provinces_gdf['tooltip_html_content'] = provinces_gdf.apply(
        lambda row: generate_tooltip_html(
            {'properties': row.to_dict()},
            province_info
        ), axis=1
    )

    map_styled_province_function = get_styled_province_function(province_info)

    tooltip_field = folium.features.GeoJsonTooltip(
        fields=['tooltip_html_content'],
        aliases=[''],
        localize=False,
        sticky=True,
        labels=False,
        max_width=800
    )

    folium.GeoJson(
        provinces_gdf,
        name='Areas (Provinces under Active Advisories)',
        style_function=map_styled_province_function,
        tooltip=tooltip_field
    ).add_to(m)

    province_labels_group = folium.FeatureGroup(name="Province Labels (Advised Areas)")
    province_labels_group.add_to(m)

    for index, row in provinces_gdf.iterrows():
        province_name = row['adm2_en']
        if isinstance(province_name, str):
            cleaned_province_name_lower = province_name.replace('Province of ', '').strip().lower()

            if cleaned_province_name_lower in province_info:
                label_lat = row.get('label_lat')
                label_lon = row.get('label_lon')

                final_label_coords = None

                if pd.notna(label_lat) and pd.notna(label_lon):
                    try:
                        final_label_coords = [float(label_lat), float(label_lon)]
                    except ValueError:
                        print(f"Warning: Non-numeric label_lat/lon for {province_name}. Falling back to polylabel.")
                        final_label_coords = None
                else:
                    print(f"Info: Missing label_lat/lon for {province_name}. Falling back to polylabel.")

                if final_label_coords is None:
                    if row.geometry:
                        geometry_for_label = None

                        if not row.geometry.is_valid:
                            try:
                                repaired_geometry = make_valid(row.geometry)
                                if repaired_geometry and not repaired_geometry.is_empty and repaired_geometry.is_valid:
                                    geometry_for_label = repaired_geometry
                            except Exception as e:
                                print(f"Error repairing geometry for {province_name}: {e}")
                                geometry_for_label = None
                        else:
                            geometry_for_label = row.geometry

                        if geometry_for_label and geometry_for_label.is_valid:
                            label_point = None
                            try:
                                if geometry_for_label.geom_type == 'Polygon':
                                    label_point = polylabel(geometry_for_label, tolerance=0.001)
                                elif geometry_for_label.geom_type == 'MultiPolygon':
                                    largest_part = None
                                    max_area = -1
                                    for part in geometry_for_label.geoms:
                                        if isinstance(part, Polygon) and part.is_valid:
                                            part_area = part.area
                                            if part_area > max_area:
                                                largest_part = part
                                                max_area = part_area
                                    if largest_part:
                                        label_point = polylabel(largest_part, tolerance=0.001)

                                if isinstance(label_point, Point):
                                    final_label_coords = [label_point.y, label_point.x]
                                else:
                                    print(f"Warning: polylabel returned non-Point for {province_name}. Skipping label.")
                            except Exception as e:
                                print(f"Error calculating polylabel for {province_name}: {e}")
                                pass
                
                if final_label_coords:
                    label_html = f'<div style="font-size: 8pt; color: black; text-align: center; white-space: nowrap; text-shadow: -1px -1px 0 #FFF, 1px -1px 0 #FFF, -1px 1px 0 #FFF, 1px 1px 0 #FFF;">{province_name}</div>'

                    folium.Marker(
                        location=final_label_coords,
                        icon=folium.DivIcon(
                            html=label_html,
                            class_name="province-label",
                            icon_size=(120, 20),
                            icon_anchor=(60, 10)
                        ),
                    ).add_to(province_labels_group)
                else:
                    print(f"Skipping label for {province_name} due to missing or invalid coordinates (no custom and no valid polylabel).")

    full_viewport_css = """
    <style>
        html, body {
            width: 100%;
            height: 100%;
            margin: 0;
            padding: 0;
            overflow: hidden;
        }
        .folium-map {
            position: absolute;
            top: 0;
            left: 0;
            width: 100% !important;
            height: 100% !important;
        }
    </style>
    """
    m.get_root().html.add_child(folium.Element(full_viewport_css))
    
    province_label_css = """
    <style>
        .province-label {
        }
        .province-label div {
            position: relative;
            transform: translate(-50%, -50%);
            left: 50%;
            top: 50%;
            font-size: 8pt;
            color: black;
            text-align: center;
            white-space: nowrap;
            text-shadow: -1px -1px 0 #FFF, 1px -1px 0 #FFF, -1px 1px 0 #FFF, 1px 1px 0 #FFF;
        }
    </style>
    """
    m.get_root().html.add_child(folium.Element(province_label_css))

    move_zoom_control_js_html = f"""
    <style>
        .leaflet-control-zoom a {{
            display: flex;
            justify-content: center;
            align-items: center;
            text-decoration: none;
            font-weight: bold;
            font-size: 1.2em;
        }}

        .leaflet-control-zoom-in,
        .leaflet-control-zoom-out {{
            line-height: normal !important;
        }}
    </style>
    <script>
        document.addEventListener('DOMContentLoaded', function() {{
            setTimeout(function() {{
                var zoomControl = document.querySelector('.leaflet-control-zoom');

                if (zoomControl) {{
                    var controlContainer = zoomControl.parentNode;

                    if (controlContainer) {{
                        controlContainer.style.position = 'absolute';
                        controlContainer.style.bottom = '24px';
                        controlContainer.style.right = '10px';
                        controlContainer.style.top = 'auto';
                        controlContainer.style.left = 'auto';

                        console.log('Zoom control repositioned via direct CSS properties.');
                    }} else {{
                        console.warn('Parent container for zoom control not found.');
                    }}
                }} else {{
                    console.warn('Zoom control element (.leaflet-control-zoom) not found in DOM after delay.');
                }}
            }}, 000);
        }});
    </script>
    """
    m.get_root().html.add_child(folium.Element(move_zoom_control_js_html))
    
    folium.LayerControl().add_to(m)
    m.fit_bounds([southwest, northeast])
    map_output_path = "gfa.html"
    m.save(map_output_path)
    print(f"\nInteractive map saved to {map_output_path}")

def take_map_screenshot(html_file_path, output_image_path):
    print(f"\nAttempting to take screenshot of {html_file_path}...")
    
    chrome_options = Options()
    chrome_options.add_argument("--headless")
    chrome_options.add_argument("--no-sandbox")
    chrome_options.add_argument("--disable-dev-shm-usage")
    chrome_options.add_argument("--window-size=810,1080")
    chrome_options.add_argument("--hide-scrollbars")
    chrome_options.add_argument("--force-device-scale-factor=1")

    try:
        service = Service('./chromedriver.exe')
        driver = webdriver.Chrome(service=service, options=chrome_options)
    except Exception as e:
        print(f"Error initializing WebDriver: {e}")
        print("Please ensure ChromeDriver is installed and its path is correctly specified.")
        print("You can download ChromeDriver from: https://chromedriver.chromium.org/downloads")
        return

    try:
        driver.get(f"file:///Z:/04 OTHER FILES/13 Presentations/2. IBF/GFA Map/gfa.html")

        WebDriverWait(driver, 20).until(
            EC.presence_of_element_located((By.CLASS_NAME, 'leaflet-container'))
        )
        # print("Map container detected. Waiting a bit more for full rendering...")
        time.sleep(1)

        map_id = driver.execute_script("""
            var mapElement = document.querySelector('.leaflet-container');
            if (mapElement && mapElement.id) {
                return mapElement.id;
            }
            return null;
        """)

        if map_id:
            # print(f"Found map ID: {map_id}. Panning map view to the right for screenshot...")
            driver.execute_script(f"{map_id}.panBy([-110, 5]);")
            time.sleep(3)
        # else:
            # print("Could not find the map container ID. Cannot pan the map.")

        driver.save_screenshot(output_image_path)
        print(f"Screenshot saved to {output_image_path}.")

    except Exception as e:
        print(f"An error occurred during screenshot capture: {e}")
        traceback.print_exc()
    finally:
        driver.quit()
        # print("WebDriver closed.")

user_date_input = input("Enter the date (YYYY-MM-DD), example 2025-01-01: ")
user_am_pm_input = input("Enter 'am' or 'pm': ").lower()

start_time = time.perf_counter()

gfa_identifiers = extract_gfa_identifiers(user_date_input, user_am_pm_input)

if gfa_identifiers:
    all_raw_gfa_cap_data = {}
    for identifier in gfa_identifiers:
        print(f"Downloading and parsing CAP file: {identifier}")
        cap_data = extract_cap_data(identifier)
        if cap_data:
            all_raw_gfa_cap_data[identifier] = cap_data

    if all_raw_gfa_cap_data:
        print("\nFiltering advisories to remove cancellations...")
        filtered_gfa_data_for_map = filter_active_advisories(all_raw_gfa_cap_data)

        if filtered_gfa_data_for_map:
            map_output_path = "gfa.html"
            create_flood_map(filtered_gfa_data_for_map, province_geojson_path="PH_Adm2_ProvDists.WGS84.mod.geojson")
            screenshot_output_path = "gfamap.png"
            take_map_screenshot(map_output_path, screenshot_output_path)
        else:
            print("After filtering, no active General Flood Advisory data remains for mapping.")
    else:
        print("No CAP data could be extracted for the specified General Flood Advisory identifiers (even before filtering).")
else:
    print("No General Flood Advisory identifiers found matching your criteria.")

end_time = time.perf_counter()
duration = end_time - start_time
minutes = int(duration // 60)
seconds = duration % 60

print(f"\nProcess completed in {duration:.0f} seconds.")
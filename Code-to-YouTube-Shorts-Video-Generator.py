import tkinter as tk
from tkinter import filedialog, scrolledtext, font as tkFont, Menu, messagebox
import moviepy.editor as mp
from PIL import Image, ImageDraw, ImageFont
import numpy as np
import string
import re
import threading
from collections import defaultdict
import os

class LRUCache:
    def __init__(self, capacity):
        self.capacity = capacity
        self.cache = {}

    def get(self, key):
        if key in self.cache:
            value = self.cache.pop(key)
            self.cache[key] = value
            return value
        return None

    def put(self, key, value):
        if key in self.cache:
            del self.cache[key]
        elif len(self.cache) >= self.capacity:
            self.cache.pop(next(iter(self.cache)))
        self.cache[key] = value

class VideoGenerator:
    WIDTH = 1080
    HEIGHT = 1920
    TOP_GAP = 200
    FONT_SIZE = 40
    FPS = 10
    BATCH_SIZE = 10
    MAX_CACHE_SIZE = 100
    LINE_CHUNK_SIZE = 32
    SERIAL_NUMBER_MARGIN = 50
    MAIN_TEXT_MARGIN = 30
    LINE_SPACING = 2

    KEYWORDS = {
        "java": {"abstract", "assert", "boolean", "break", "byte", "case", "catch",
                 "char", "class", "const", "continue", "default", "do", "double",
                 "else", "enum", "extends", "final", "finally", "float", "for",
                 "goto", "if", "implements", "import", "instanceof", "int",
                 "interface", "long", "native", "new", "package", "private",
                 "protected", "public", "return", "short", "static", "strictfp",
                 "super", "switch", "synchronized", "this", "throw", "throws",
                 "transient", "try", "void", "volatile", "while"
                 },
        "cpp": {"auto", "break", "case", "char", "const", "continue", "default",
                "do", "double", "else", "enum", "extern", "float", "for", "goto",
                "if", "inline", "int", "long", "register", "return", "short",
                "signed", "sizeof", "static", "struct", "switch", "typedef",
                "union", "unsigned", "void", "volatile", "while", "bool", "catch",
                "class", "const_cast", "delete", "dynamic_cast", "explicit",
                "export", "false", "friend", "mutable", "namespace", "new",
                "operator", "private", "protected", "public", "reinterpret_cast",
                "static_cast", "template", "this", "throw", "true", "try", "typename",
                "using", "virtual", "wchar_t"
                },
        "python": {"False", "None", "True", "and", "as", "assert", "async", "await",
                   "break", "class", "continue", "def", "del", "elif", "else", "except",
                   "finally", "for", "from", "global", "if", "import", "in", "is", "lambda",
                   "nonlocal", "not", "or", "pass", "raise", "return", "try", "while", "with",
                   "yield"
                   }
    }

    COMMENT_PATTERN = r"//.*?$|/\*.*?\*/"
    STRING_PATTERN = r"\".*?\"|'.*?'"
    NUMBER_PATTERN = r"\b\d+(\.\d+)?\b"
    OPERATOR_PATTERN = r"[" + re.escape("".join(['+', '-', '*', '/', '=', '==', '!=', '<', '>', '<=', '>=', '&&', '||', '!', '&', '|', '^'])) + r"]"

    def __init__(self, root):
        self.root = root
        self.setup_gui()
        self.setup_menu()
        self.cache = LRUCache(self.MAX_CACHE_SIZE)
        self.executor = None
        self.character_widths = self.compute_character_widths()

        self.keyword_patterns = defaultdict(lambda: re.compile(''))
        for language, keywords in self.KEYWORDS.items():
            self.keyword_patterns[language] = re.compile(r"\b(" + "|".join(map(re.escape, keywords)) + r")\b", re.IGNORECASE)
        self.comment_regex = re.compile(self.COMMENT_PATTERN, re.DOTALL | re.MULTILINE)
        self.string_regex = re.compile(self.STRING_PATTERN)
        self.number_regex = re.compile(self.NUMBER_PATTERN)
        self.operator_regex = re.compile(self.OPERATOR_PATTERN)

        self.language_var = tk.StringVar(self.root)
        self.language_var.set("Select Language")  # Default option
        self.language_var.trace_add("write", lambda *args: self.highlight_keywords())

    def setup_gui(self):
        self.arial_font = tkFont.Font(family="Arial", size=12)
        self.text_area = scrolledtext.ScrolledText(self.root, undo=True, font=self.arial_font, wrap="word")
        self.text_area.pack(fill=tk.BOTH, expand=True)
        self.text_area.bind("<KeyRelease>", self.highlight_keywords)
        self.text_area.tag_configure("keyword", foreground="blue")
        self.text_area.tag_configure("comment", foreground="green")
        self.text_area.tag_configure("string", foreground="red")
        self.text_area.tag_configure("number", foreground="purple")
        self.text_area.tag_configure("operator", foreground="brown")
        self.root.protocol("WM_DELETE_WINDOW", self.cleanup)

    def setup_menu(self):
        menu_bar = tk.Menu(self.root)
        self.root.config(menu=menu_bar)

        file_menu = tk.Menu(menu_bar, tearoff=False)
        menu_bar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Save as MP4", command=self.save_file_as_mp4)
        file_menu.add_separator()

        language_menu = tk.Menu(menu_bar, tearoff=False)
        menu_bar.add_cascade(label="Language", menu=language_menu)
        for language in ["Java", "C++", "Python"]:
            language_menu.add_command(label=language, command=lambda lang=language: self.update_language(lang))

    def cleanup(self):
        print("Cleaning up resources.")
        if self.executor and self.executor.is_alive():
            self.executor.join()
        self.root.quit()
        self.root.destroy()
        print("Cleanup complete.")

    def highlight_keywords(self, event=None):
        content = self.text_area.get("1.0", tk.END)
        for tag in ["keyword", "comment", "string", "number", "operator"]:
            self.text_area.tag_remove(tag, "1.0", tk.END)
        
        selected_language = self.language_var.get()
        if selected_language == "Select Language":
            self.default_syntax_highlighting(content)
        else:
            language_keywords = self.KEYWORDS.get(selected_language.lower(), set())
            keyword_pattern = re.compile(r"\b(" + "|".join(map(re.escape, language_keywords)) + r")\b", re.IGNORECASE)
            self.highlight_pattern(keyword_pattern, "keyword", content)
            self.highlight_pattern(self.comment_regex, "comment", content)
            self.highlight_pattern(self.string_regex, "string", content)
            self.highlight_pattern(self.number_regex, "number", content)
            self.highlight_pattern(self.operator_regex, "operator", content)  # Highlight operators
        
        # Highlight curly braces specifically
        self.text_area.tag_configure("brace", foreground="orange")
        brace_pattern = re.compile(r"[\[\]\(\)\{\}]")        
        self.highlight_pattern(brace_pattern, "brace", content)

    def default_syntax_highlighting(self, content):
        self.highlight_pattern(self.comment_regex, "comment", content)
        self.highlight_pattern(self.string_regex, "string", content)
        self.highlight_pattern(self.number_regex, "number", content)
        self.highlight_pattern(self.operator_regex, "operator", content)

    def highlight_pattern(self, regex, tag, content):
        for match in regex.finditer(content):
            start_index = match.start()
            end_index = match.end()
            self.text_area.tag_add(tag, f"1.0+{start_index}c", f"1.0+{end_index}c")

    def save_file_as_mp4(self):
        file_path = filedialog.asksaveasfilename(defaultextension=".mp4", filetypes=[("MP4 Files", "*.mp4"), ("All Files", "*.*")])
        if file_path:
            if self.executor and self.executor.is_alive():
                messagebox.showwarning("Warning", "A video is already being generated. Please wait.")
            else:
                self.executor = threading.Thread(target=self.generate_video, args=(file_path,))
                self.executor.start()

    def generate_video(self, file_path):
        try:
            frames_np = self.generate_frames(self.text_area.get("1.0", "end-1c"))
            total_frames = len(frames_np)
            duration = min(max(total_frames / 15, 1), 15)
            fps = total_frames / duration
            clip = mp.ImageSequenceClip(frames_np, fps=fps)

            # Extend the video duration by repeating the last frame for 7 seconds
            if total_frames > 0:
                last_frame = frames_np[-1]
                extension_duration = 7
                extension_frames = [last_frame] * int(extension_duration * fps)
                extension_clip = mp.ImageSequenceClip(extension_frames, fps=fps)
                final_clip = mp.concatenate_videoclips([clip, extension_clip])
            else:
                final_clip = clip

            final_clip.write_videofile(file_path, codec="libx264")
            tk.messagebox.showinfo("Success", "Video saved successfully.")
        except Exception as e:
            tk.messagebox.showerror("Error", f"An error occurred while generating the video: {e}")

    def compute_character_widths(self):
        font = self.load_fonts()
        return {char: font.getbbox(char)[2] for char in string.ascii_letters + string.digits + string.punctuation + ' '}

    def load_fonts(self):
        if not hasattr(self, 'image_font'):
            font_file_path = "arial.ttf"  # Ensure this font file is in the same directory as your script
            try:
                self.image_font = ImageFont.truetype(font_file_path, self.FONT_SIZE)
            except IOError:
                tk.messagebox.showerror("Font Error", "Arial font file not found.")
                self.root.quit()
            self.line_height = self.image_font.getbbox("hg")[3] - self.image_font.getbbox("hg")[1]
        return self.image_font

    def wrap_text(self, text, max_width):
        lines = []
        words = text.split(' ')
        current_line = []
        current_width = 0

        for word in words:
            word_width = sum(self.character_widths.get(char, 0) for char in word)
            space_width = self.character_widths.get(' ', 0)
            if current_width + word_width + space_width <= max_width:
                current_line.append(word)
                current_width += word_width + space_width
            else:
                lines.append(' '.join(current_line))
                current_line = [word]
                current_width = word_width + space_width

        if current_line:
            lines.append(' '.join(current_line))

        return lines

    def generate_chunk_frames(self, chunk_lines, start_line_number):
        frames = []
        width, height = self.WIDTH, self.HEIGHT
        y = self.TOP_GAP
        self.text_area.delete("1.0", tk.END)
        self.text_area.insert(tk.END, '\n'.join(chunk_lines))
        self.highlight_keywords()
        image = Image.new("RGB", (width, height), "white")
        draw = ImageDraw.Draw(image)
        text_position = 0

        line_number = start_line_number  # Initialize line number counter

        # Draw a vertical line to separate the serial number margin and the main text
        draw.line([(self.SERIAL_NUMBER_MARGIN, 0), (self.SERIAL_NUMBER_MARGIN, height)], fill="black", width=2)

        for line_index, line in enumerate(chunk_lines):
            wrapped_lines = self.wrap_text(line, width - 2 * self.MAIN_TEXT_MARGIN)
            first_line_of_chunk = True  # Flag to track the first line of the chunk

            # Check if the current line is a comment
            is_comment = re.match(self.COMMENT_PATTERN, line.strip())

            for wrapped_line_index, wrapped_line in enumerate(wrapped_lines):
                # Calculate the width of the serial number text
                serial_number_text = str(line_number)
                serial_number_width = draw.textbbox((0, 0), serial_number_text, font=self.image_font)[2]

                # Calculate the x-coordinate to center the serial number text within the margin
                serial_number_x = (self.SERIAL_NUMBER_MARGIN - serial_number_width) / 2

                # Draw the serial number
                draw.rectangle([0, y, self.SERIAL_NUMBER_MARGIN, y + self.line_height], fill="lightgray")
                draw.text((serial_number_x, y), serial_number_text, fill="black", font=self.image_font)

                # Calculate starting position for main text
                x = self.SERIAL_NUMBER_MARGIN + self.MAIN_TEXT_MARGIN  # Updated x-coordinate to align with serial numbers
                for char in wrapped_line:
                    char_width = self.character_widths.get(char, 0)
                    char_tags = self.text_area.tag_names(f"1.0+{text_position}c")
                    
                    # Determine the fill color based on tag or comment status
                    if is_comment:
                        if re.match(self.NUMBER_PATTERN, char):
                            fill_color = "purple"  # Highlight numbers in comments
                        elif re.match(self.OPERATOR_PATTERN, char):
                            fill_color = "brown"  # Highlight operators in comments
                        else:
                            fill_color = "green"  # Default color for comment text
                    else:
                        fill_color = "black"
                        if "keyword" in char_tags:
                            fill_color = "blue"
                        elif "comment" in char_tags:
                            fill_color = "green"
                        elif "string" in char_tags:
                            fill_color = "red"
                        elif "number" in char_tags:
                            fill_color = "purple"
                        elif "operator" in char_tags:
                            fill_color = "brown"
                        elif "brace" in char_tags:
                            fill_color = "orange"

                    # Draw the character
                    draw.text((x, y), char, fill=fill_color, font=self.image_font)
                    x += char_width
                    frame = np.array(image)
                    frames.append(frame)
                    if char != '\n':
                        text_position += 1

                y += self.line_height + self.LINE_SPACING  # Increment y position for the next line
                if y + self.line_height > height:
                    break

                text_position += 1

                # Increment line number only if it's a new logical line
                if not wrapped_line.endswith('\n'):
                    line_number += 1

        return frames

    def generate_frames(self, text):
        lines = text.split("\n")
        total_frames = []
        current_line_number = 1  # Initialize the line number

        for i in range(0, len(lines), self.LINE_CHUNK_SIZE):
            chunk_lines = lines[i:i+self.LINE_CHUNK_SIZE]
            chunk_frames = self.generate_chunk_frames(chunk_lines, current_line_number)
            total_frames.extend(chunk_frames)
            current_line_number += len(chunk_lines)  # Update line number for the next chunk

        return total_frames

    def update_language(self, language):
        self.language_var.set(language)
        self.highlight_keywords()

if __name__ == "__main__":
    root = tk.Tk()
    root.geometry("800x600")
    root.title("Code to Video Converter")
    app = VideoGenerator(root)
    root.mainloop()

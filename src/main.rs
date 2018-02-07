#![allow(dead_code, unused_variables)]

use std::str::FromStr;

/// Parse the string `s` as a coordinate pair, like `"400x600"` or `"1.0,0.5"`.
///
/// Specifically, `s` should have the form <left><sep><right>, where <sep> is
/// the character given by the `separator` argument, and <left> and <right> are both
/// strings that can be parsed by `T::from_str`.
///
/// If `s` has the proper form, return `Some<(x, y)>`. If it doesn't parse
/// correctly, return `None`.
fn parse_pair<T: FromStr>(s: &str, separator: char) -> Option<(T, T)> {
    match s.find(separator) {
        None => None,
        Some(index) => {
            match (T::from_str(&s[..index]), T::from_str(&s[index + 1..])) {
                (Ok(l), Ok(r)) => Some((l, r)),
                _ => None
            }
        }
    }
}

#[test]
fn test_parse_pair() {
    assert_eq!(parse_pair::<i32>("",        ','), None);
    assert_eq!(parse_pair::<i32>("10,",     ','), None);
    assert_eq!(parse_pair::<i32>(",10",     ','), None);
    assert_eq!(parse_pair::<i32>("10,20",   ','), Some((10, 20)));
    assert_eq!(parse_pair::<i32>("10,20xy", ','), None);
    assert_eq!(parse_pair::<f64>("0.5x",    'x'), None);
    assert_eq!(parse_pair::<f64>("0.5x1.5", 'x'), Some((0.5, 1.5)));
}

/// Return the point on the complex plane corresponding to a given pixel in the
/// bitmap.
///
/// `bounds` is a pair giving the width and height of the bitmap. `pixel` is a
/// pair indicating a particular pixel in that bitmap. The `upper_left` and
/// `lower_right` parameters are points on the complex plane designating the
/// area our bitmap covers.
fn pixel_to_point(bounds: (usize, usize),
                  pixel: (usize, usize),
                  upper_left: (f64, f64),
                  lower_right: (f64, f64))
    -> (f64, f64)
{
    // It might be nicer to find the position of the *middle* of the pixel,
    // instead of its upper left corner, but this is easier to write tests for.
    let (width, height) = (lower_right.0 - upper_left.0,
                           upper_left.1 - lower_right.1);
    (upper_left.0 + pixel.0 as f64 * width  / bounds.0 as f64,
     upper_left.1 - pixel.1 as f64 * height / bounds.1 as f64)
}

#[test]
fn test_pixel_to_point() {
    assert_eq!(pixel_to_point((100, 100), (25, 75),
                              (-1.0, 1.0), (1.0, -1.0)),
               (-0.5, -0.5));
}

extern crate num;
use num::Complex;

/// Try to determine whether the complex number `c` is in the Mandelbrot set.
///
/// A number `c` is in the set if, starting with zero, repeatedly squaring and
/// adding `c` never causes the number to leave the circle of radius 2 centered
/// on the origin; the number instead orbits near the origin forever. (If the
/// number does leave the circle, it eventually flies away to infinity.)
///
/// If after `limit` iterations our number has still not left the circle, return
/// `None`; this is as close as we come to knowing that `c` is in the set.
///
/// If the number does leave the circle before we give up, return `Some(i)`, where
/// `i` is the number of iterations it took.
fn escapes(c: &Complex<f64>, mut z: Complex<f64>, limit: u32) -> Option<u32> {
    for i in 0..limit {
        z = z*z*z + c;
        if z.norm_sqr() > 4.0 {
            return Some(i);
        }
    }

    return None;
}

fn iter_to_gray(it: u32, limit: u32, elbow: (u32, f64)) -> f64
{
    if it <= elbow.0 {
        it as f64 * elbow.1 / elbow.0 as f64
    } else {
        (it - elbow.0) as f64 * (1. - elbow.1) / (limit - elbow.0) as f64 + elbow.1
    }
}

#[test]
fn test_iter_to_gray() {
    assert_eq!(iter_to_gray(0, 100, (4, 0.50)), 0.0);
    assert_eq!(iter_to_gray(1, 100, (4, 0.50)), 0.125);
    assert_eq!(iter_to_gray(2, 100, (4, 0.50)), 0.25);
    assert_eq!(iter_to_gray(3, 100, (4, 0.50)), 0.375);
    assert_eq!(iter_to_gray(4, 100, (4, 0.50)), 0.5);

    assert_eq!(iter_to_gray(5, 100, (4, 0.50)), 0.5052083333333334);
}

/// Render a rectangle of the Julia set for `control` into a buffer of pixels.
///
/// The `bounds` argument gives the width and height of the buffer `pixels`,
/// which holds one grayscale pixel per byte. The `upper_left` and `lower_right`
/// arguments specify points on the complex plane corresponding to the upper
/// left and lower right corners of the pixel buffer.
fn render(control: (f64, f64),
          pixels: &mut [u8], bounds: (usize, usize),
          upper_left: (f64, f64), lower_right: (f64, f64))
{
    assert!(pixels.len() == bounds.0 * bounds.1);

    let limit = 100;
    let control = Complex { re: control.0, im: control.1 };

    for r in 0 .. bounds.1 {
        for c in 0 .. bounds.0 {
            let point = pixel_to_point(bounds, (c, r),
                                       upper_left, lower_right);
            let point = Complex { re: point.0, im: point.1 };

            let gray = if let Some(it) = escapes(&control, point, limit) {
                // Map the iteration count to value between 0 and 1.
                // iteration counts 0..4 cover 0.0..0.16, counts
                // 5..limit cover 0.16 to 1.0.
                iter_to_gray(it, limit, (4, 0.20))
            } else {
                1.0
            };

            assert!(0.0 <= gray && gray <= 1.0);

            // Brighten things up a bit: invert, cube to push it towards zero,
            // and revert.
            let gray = 1.0 - gray;
            let gray = gray * gray * gray * gray;

            pixels[r * bounds.0 + c] = f64::floor(gray * 255.0) as u8;
        }
    }
}

extern crate image;

use std::fs::File;
use std::io::Result;
use image::png::PNGEncoder;
use image::ColorType;

/// Write the buffer `pixels`, whose dimensions are given by `bounds`, to the
/// file named `filename`.
fn write_bitmap(filename: &str, pixels: &[u8], bounds: (usize, usize))
    -> Result<()>
{
    let output = try!(File::create(filename));

    let encoder = PNGEncoder::new(output);
    try!(encoder.encode(&pixels[..],
                        bounds.0 as u32, bounds.1 as u32,
                        ColorType::Gray(8)));

    Ok(())
}


use std::time::{Instant, Duration};

fn measure_elapsed_time<F: FnOnce()>(f: F) -> Duration {
    let t0 = Instant::now();
    f();
    Instant::now() - t0
}


extern crate rayon;

use std::io::Write;
use rayon::prelude::*;

fn main() {
    let args : Vec<String> = std::env::args().collect();

    if args.len() != 6 {
        writeln!(std::io::stderr(),
                 "Usage: mandelbrot FILE PIXELS UPPERLEFT LOWERRIGHT C")
            .unwrap();
        writeln!(std::io::stderr(),
                 "Example: {} julia.png 1000x750 -1.20,0.35 -1,0.20 0.5620127,0.39680684",
                 args[0])
            .unwrap();
        std::process::exit(1);
    }

    let bounds = parse_pair(&args[2], 'x')
        .expect("error parsing image dimensions");
    let upper_left = parse_pair(&args[3], ',')
        .expect("error parsing upper left corner point");
    let lower_right = parse_pair(&args[4], ',')
        .expect("error parsing lower right corner point");
    let c = parse_pair(&args[5], ',')
        .expect("error parsing Julia set control point");

    let mut pixels = vec![0; bounds.0 * bounds.1];

    // Scope of slicing up `pixels` into horizontal bands.
    {
        let bands: Vec<(usize, &mut [u8])> = pixels
            .chunks_mut(bounds.0)
            .enumerate()
            .collect();

        bands.into_par_iter()
            .weight_max()
            .for_each(|(i, band)| {
                let top = i;
                let band_bounds = (bounds.0, 1);
                let band_upper_left = pixel_to_point(bounds, (0, top),
                                                     upper_left, lower_right);
                let band_lower_right = pixel_to_point(bounds, (bounds.0, top + 1),
                                                      upper_left, lower_right);
                render(c, band, band_bounds, band_upper_left, band_lower_right);
            });
    }

    write_bitmap(&args[1], &pixels, bounds).expect("error writing PNG file");
}

use chrono::TimeZone as _;
use std::fmt;

const MAX_CHRONO_NANOS: u64 = 9_223_372_036_854_775_807;
const NANOS_PER_SEC: i64 = 1E9 as i64;

/// Alias the types so we don't get confused
type ChronoDateTime = chrono::DateTime<chrono::Utc>;
type ChronoDuration = chrono::Duration;
type HifiEpoch = hifitime::Epoch;
type HifiDuration = hifitime::Duration;

/// A wrapper type for time-related conversions
#[derive(Debug, Clone, Copy)]
pub struct TimeTraveler<T>(pub T);

#[derive(Debug)]
pub struct TimeConversionError {
    message: String,
}

impl fmt::Display for TimeConversionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for TimeConversionError {}

/// Calculates the maximum valid `chrono::DateTime<Utc>`
fn max_valid_chrono_datetime() -> ChronoDateTime {
    let max_timestamp_secs = i64::MAX / 1_000_000_000;
    let max_timestamp_nanos = (i64::MAX % 1_000_000_000) as u32;

    chrono::Utc
        .timestamp_opt(max_timestamp_secs, max_timestamp_nanos)
        .unwrap()
}

/// Conversions between `TimeTraveler<hifitime::Epoch>` and `chrono::DateTime<Utc>`.
///
/// # Examples
///
/// ```
/// use chrono::{DateTime, Utc};
/// use hifitime::Epoch as HifiEpoch;
/// use time_traveler::TimeTraveler;
///
/// let hifi_epoch = HifiEpoch::from_gregorian_utc(2023, 8, 12, 15, 30, 45, 0);
/// let wrapper = TimeTraveler(hifi_epoch);
/// let chrono_datetime: DateTime<Utc> = wrapper.into();
/// assert_eq!(chrono_datetime.year(), 2023);
/// assert_eq!(chrono_datetime.month(), 8);
/// assert_eq!(chrono_datetime.day(), 12);
/// assert_eq!(chrono_datetime.hour(), 15);
/// assert_eq!(chrono_datetime.minute(), 30);
/// assert_eq!(chrono_datetime.second(), 45);
///
/// let hifi_epoch_roundtrip: TimeTraveler<HifiEpoch> = TimeTraveler(chrono_datetime);
/// assert!((hifi_epoch - hifi_epoch_roundtrip.0).abs() < HifiDuration::from_milliseconds(1.));
/// ```

/// Get a `chrono::DateTime<chrono::Utc>` from a
/// `TimeTraveler<hifitime::Epoch>`. This is only guaranteed for timestamps
/// between 1677-09-21T00:12:43.145224192 and 2262-04-11T23:47:16.854775807
/// (where `chrono::DateTime` is defined).
impl TryFrom<TimeTraveler<HifiEpoch>> for ChronoDateTime {
    type Error = TimeConversionError;

    fn try_from(wrapper: TimeTraveler<HifiEpoch>) -> Result<Self, Self::Error> {
        let max_hifitime_epoch =
            HifiEpoch::from_unix_duration(HifiDuration::from_nanoseconds(MAX_CHRONO_NANOS as f64));

        // Compare and convert
        if wrapper.0 <= max_hifitime_epoch {
            Ok(chrono::DateTime::from_timestamp_nanos(
                wrapper.0.duration.truncated_nanoseconds() as i64,
            ))
        } else {
            Err(TimeConversionError {
                message: format!(
                    "Epoch {:?} is out of bounds for chrono::DateTime (max = {:?})",
                    wrapper.0,
                    max_valid_chrono_datetime()
                ),
            })
        }
    }
}

/// Get a `hifitime::Epoch` from a
/// `TimeTraveler<chrono::DateTime<chrono::Utc>>`. Timestamps between
/// 1677-09-21T00:12:43.145224192 and 2262-04-11T23:47:16.854775807 are
/// derived from nanoseconds since Unix epoch (1970-01-01T00:00:00Z). Timestamps
/// outside this range are derived from microseconds since Unix epoch due to
/// limitations within `chrono`.
impl From<TimeTraveler<ChronoDateTime>> for HifiEpoch {
    fn from(wrapper: TimeTraveler<ChronoDateTime>) -> Self {
        let duration = match wrapper.0.timestamp_nanos_opt() {
            Some(nanos) => HifiDuration::from_nanoseconds(nanos as f64),
            None => HifiDuration::from_microseconds(wrapper.0.timestamp_micros() as f64),
        };
        return HifiEpoch::from_unix_duration(duration);
    }
}

/// Conversions between `TimeTraveler<hifitime::Duration>` and `chrono::Duration`.
///
/// # Examples
///
/// ```
/// use chrono::Duration as ChronoDuration;
/// use hifitime::Duration as HifiDuration;
/// use time_traveler::TimeTraveler;
///
/// let hifi_duration = HifiDuration::from_days(365.) + HifiDuration::from_hours(6.);
/// let wrapper = TimeTraveler(hifi_duration);
/// let chrono_duration: ChronoDuration = wrapper.into();
/// assert_eq!(chrono_duration.num_days(), 365);
/// assert_eq!(chrono_duration.num_hours() % 24, 6);
///
/// let hifi_duration_roundtrip: TimeTraveler<HifiDuration> = TimeTraveler(chrono_duration);
/// assert!((hifi_duration - hifi_duration_roundtrip.0).abs() < HifiDuration::from_milliseconds(1.));
/// ```

/// Get a `chrono::Duration` from a `TimeTraveler<hifitime::Duration>`
impl TryFrom<TimeTraveler<HifiDuration>> for ChronoDuration {
    type Error = TimeConversionError;

    fn try_from(wrapper: TimeTraveler<HifiDuration>) -> Result<Self, Self::Error> {
        let (centuries, nanos) = wrapper.0.to_parts();
        let days = centuries as i64 * 36524; // Convert centuries to days.
        let chrono_days = ChronoDuration::days(days);
        let chrono_nanos = ChronoDuration::nanoseconds(nanos as i64);
        Ok(chrono_days + chrono_nanos)
    }
}

/// Get a `hifitime::Duration` from a `TimeTraveler<chrono::Duration>`
impl From<TimeTraveler<ChronoDuration>> for HifiDuration {
    fn from(wrapper: TimeTraveler<ChronoDuration>) -> Self {
        // for some reason this always ends up being a chrono::TimeDelta instead
        // so let's roll with it. TimeDelta is safer anyways.
        let nanos = wrapper.0.subsec_nanos() as i64 + wrapper.0.num_seconds() * NANOS_PER_SEC;
        HifiDuration::from_nanoseconds(nanos as f64)
    }
}

#[cfg(test)]
mod tests {
    use std::i64;

    use chrono::{Datelike as _, Timelike as _};

    use super::*;

    #[test]
    fn test_max_chrono_datetime() {
        let nanos_result = max_valid_chrono_datetime().timestamp_nanos_opt();
        assert!(nanos_result.is_some());
        let nanos = nanos_result.unwrap();
        assert_eq!(nanos, 9_223_372_036_854_775_807);
    }

    // Helper function to compare HifiEpoch and DateTime<Utc>. This proves
    // whether the `chrono` and `hifitime` timestamps are equivalent to 32-bit
    // precision (chrono's limit).
    fn assert_epoch_datetime_eq(epoch: hifitime::Epoch, datetime: chrono::DateTime<chrono::Utc>) {
        // NOTE(phil): Don't use this to test the limits of chrono.
        // chrono::DateTime is not guaranteed for roundtrip conversion unless we
        // use .timestamp_nanos_opt()
        let (y, m, d, h, min, s, ns) = epoch.to_gregorian_utc();
        assert_eq!(datetime.year(), y as i32);
        assert_eq!(datetime.month(), m as u32);
        assert_eq!(datetime.day(), d as u32);
        assert_eq!(datetime.hour(), h as u32);
        assert_eq!(datetime.minute(), min as u32);
        assert_eq!(datetime.second(), s as u32);
        assert_eq!(datetime.nanosecond(), ns);
    }
    // Helper function to compare HifiEpoch and DateTime<Utc> using nanoseconds.
    fn assert_epoch_datetime_nanos_eq(
        epoch: hifitime::Epoch,
        datetime: chrono::DateTime<chrono::Utc>,
    ) {
        let epoch_nanos = epoch.duration.truncated_nanoseconds();
        let datetime_nanos_result = datetime.timestamp_nanos_opt();
        assert!(datetime_nanos_result.is_some());
        let datetime_nanos = datetime_nanos_result.unwrap();
        assert_eq!(epoch_nanos, datetime_nanos);
    }

    // Helper function to compare HifiDuration and ChronoDuration. Only accurate
    // to i64 nanoseconds.
    fn assert_duration_eq(hifi: hifitime::Duration, chrono: chrono::Duration) {
        let chrono_result = chrono.num_nanoseconds();
        assert!(chrono_result.is_some());
        let chrono_nanos = chrono_result.unwrap();
        assert!(
            (hifi.truncated_nanoseconds() - chrono_nanos).abs() < 1_000,
            "hifi = {:} nanos, chrono = {:} nanos, diff = {:}",
            hifi.truncated_nanoseconds(),
            chrono_nanos.abs(),
            (hifi.truncated_nanoseconds() - chrono_nanos).abs()
        );
    }

    #[test]
    fn test_hifi_to_chrono_utc() {
        let hifi_epoch = HifiEpoch::from_gregorian_utc(2023, 8, 12, 15, 30, 45, 0);
        let chrono_utc_result = ChronoDateTime::try_from(TimeTraveler(hifi_epoch));
        assert!(
            chrono_utc_result.is_ok(),
            "Conversion to chrono::DateTime<Utc> failed"
        );
        let chrono_utc = chrono_utc_result.unwrap();
        assert_epoch_datetime_nanos_eq(hifi_epoch, chrono_utc);
    }

    #[test]
    fn test_chrono_to_hifi_epoch() {
        let chrono_datetime = chrono::Utc
            .with_ymd_and_hms(2023, 8, 12, 15, 30, 45)
            .unwrap();
        let hifi_epoch: HifiEpoch = TimeTraveler(chrono_datetime).into();
        assert_epoch_datetime_eq(hifi_epoch, chrono_datetime);
    }

    #[test]
    fn test_hifi_duration_to_chrono_duration() {
        let hifi_duration = HifiDuration::from_days(365.) + HifiDuration::from_hours(6.);
        let chrono_duration_result = ChronoDuration::try_from(TimeTraveler(hifi_duration));
        assert!(
            chrono_duration_result.is_ok(),
            "Conversion to chrono::Duration failed"
        );
        let chrono_duration = chrono_duration_result.unwrap();
        assert_duration_eq(hifi_duration, chrono_duration);
    }

    #[test]
    fn test_chrono_duration_to_hifi_duration() {
        let chrono_duration = chrono::Duration::days(365) + chrono::Duration::hours(6);
        let hifi_duration: HifiDuration = TimeTraveler(chrono_duration).into();
        assert_duration_eq(hifi_duration, chrono_duration);
    }

    #[test]
    fn test_roundtrip_epoch_conversion() {
        let original_epoch = HifiEpoch::from_gregorian_utc(2023, 8, 12, 15, 30, 45, 123_456_789);

        // Convert original_epoch to chrono::DateTime<Utc> using the `TryFrom` trait
        let chrono_datetime_result = ChronoDateTime::try_from(TimeTraveler(original_epoch));
        assert!(
            chrono_datetime_result.is_ok(),
            "Conversion to chrono::DateTime<Utc> failed"
        );

        // Get the chrono::DateTime<Utc> value
        let chrono_datetime = chrono_datetime_result.unwrap();

        // Convert back to hifitime::Epoch
        let roundtrip_epoch: HifiEpoch = TimeTraveler(chrono_datetime).into();
        assert_eq!(original_epoch, roundtrip_epoch);
    }

    #[test]
    fn test_roundtrip_duration_conversion() {
        let original_duration = HifiDuration::from_days(365.)
            + HifiDuration::from_hours(6.)
            + HifiDuration::from_nanoseconds(123_456_789.);
        let chrono_duration_result = ChronoDuration::try_from(TimeTraveler(original_duration));
        assert!(
            chrono_duration_result.is_ok(),
            "Conversion to chrono::Duration failed"
        );
        let chrono_duration = chrono_duration_result.unwrap();
        let roundtrip_duration: HifiDuration = TimeTraveler(chrono_duration).into();
        assert!(
            (original_duration - roundtrip_duration).abs() < HifiDuration::from_milliseconds(1.)
        );
    }

    // Edge case tests
    #[test]
    fn test_unix_epoch_conversion() {
        let hifi_unix_epoch: HifiEpoch = HifiEpoch::from_gregorian_utc(1970, 1, 1, 0, 0, 0, 0);
        let chrono_unix_epoch_result = ChronoDateTime::try_from(TimeTraveler(hifi_unix_epoch));
        assert!(
            chrono_unix_epoch_result.is_ok(),
            "Conversion to chrono::DateTime<Utc> failed"
        );
        let chrono_unix_epoch = chrono_unix_epoch_result.unwrap();
        assert_epoch_datetime_nanos_eq(hifi_unix_epoch, chrono_unix_epoch);
    }

    #[test]
    fn test_far_future_conversion() {
        let hifi_far_future = HifiEpoch::from_gregorian_utc(2262, 4, 11, 23, 47, 16, 854_775_807);
        let chrono_far_future_result = ChronoDateTime::try_from(TimeTraveler(hifi_far_future));
        assert!(
            chrono_far_future_result.is_ok(),
            "Conversion to chrono::DateTime<Utc> failed"
        );
        let chrono_far_future = chrono_far_future_result.unwrap();
        let chrono_far_future_nanos = chrono_far_future.timestamp_nanos_opt();
        assert!(chrono_far_future_nanos.is_some());
        assert_eq!(
            hifi_far_future.duration.truncated_nanoseconds(),
            chrono_far_future_nanos.unwrap()
        );
    }

    #[test]
    fn test_too_far_future_conversion() {
        let hifi_far_future = HifiEpoch::from_gregorian_utc(2362, 4, 11, 23, 47, 16, 854_775_800);
        let chrono_far_future_result = ChronoDateTime::try_from(TimeTraveler(hifi_far_future));
        assert!(
            chrono_far_future_result.is_err(),
            "Expected conversion to fail for too far future date"
        );
    }

    #[test]
    fn test_pre_unix_epoch_conversion() {
        let pre_unix_epoch = HifiEpoch::from_gregorian_utc(1969, 12, 31, 23, 59, 59, 999_999_999);
        let chrono_pre_unix_epoch_result = ChronoDateTime::try_from(TimeTraveler(pre_unix_epoch));
        assert!(
            chrono_pre_unix_epoch_result.is_ok(),
            "Conversion to chrono::DateTime<Utc> failed"
        );
        let chrono_pre_unix_epoch = chrono_pre_unix_epoch_result.unwrap();
        assert_epoch_datetime_nanos_eq(pre_unix_epoch, chrono_pre_unix_epoch);
    }

    #[test]
    fn test_large_duration_conversion() {
        let large_duration = HifiDuration::from_truncated_nanoseconds(i32::MAX as i64); // Approximately 500 years
        let chrono_duration_result = ChronoDuration::try_from(TimeTraveler(large_duration));
        assert!(
            chrono_duration_result.is_ok(),
            "Conversion to chrono::Duration failed"
        );
        let chrono_large_duration = chrono_duration_result.unwrap();
        assert_duration_eq(large_duration, chrono_large_duration);
    }

    #[test]
    fn test_too_large_duration_conversion() {
        let large_duration = HifiDuration::from_truncated_nanoseconds(i64::MAX); // Approximately 500 years
        let chrono_duration_result = ChronoDuration::try_from(TimeTraveler(large_duration));
        assert!(
            chrono_duration_result.is_ok(),
            "Conversion to chrono::Duration failed"
        );
        let chrono_large_duration = chrono_duration_result.unwrap();
        let chrono_result = chrono_large_duration.num_nanoseconds();
        assert!(chrono_result.is_some());
        let chrono_nanos = chrono_result.unwrap();
        assert!(
            (large_duration.total_nanoseconds() as i64 - chrono_nanos.abs() as i64).abs() > 1_000,
            "expected conversion to fail"
        );
    }

    #[test]
    fn test_small_duration_conversion() {
        let small_duration = HifiDuration::from_nanoseconds(1.);
        let chrono_duration_result = ChronoDuration::try_from(TimeTraveler(small_duration));
        assert!(
            chrono_duration_result.is_ok(),
            "Conversion to chrono::Duration failed"
        );
        let chrono_small_duration = chrono_duration_result.unwrap();
        assert_duration_eq(small_duration, chrono_small_duration);
    }
}

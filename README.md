# time-traveler
A lightweight crate for converting between types of durations and datetimes from
various timekeeping crates like `hifitime` and `chrono`.

The name "time-traveler" is a bit of wordplay. A _traveler_ is the job paperwork
carried along a work order’s lifespan. Since we are passing around _time_
structs, the wrapper around them is a _time traveler_. 🧠


`TimeTraveler<T>` around a datetime can be cast into a `hifitime::Epoch` or
`chrono::DateTime`. `TimeTraveler<T>` around a duration that be cast into a
`hifitime::Duration`, `chrono::Duration`, or `chrono::TimeDelta`.

The wrapper uses `hifitime` under the hood to preserve precision where possible.

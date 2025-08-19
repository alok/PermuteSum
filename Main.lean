import PermuteSum

import Std.Tactic.Do
import Std.Data.HashSet
open Std.Do

set_option mvcgen.warning false


def sum' (list : Array α)


def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out


theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- Focus on the part of the program which has a monadic implementation (`Id.run do ...`)
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  -- Break down into verification conditions
  mvcgen
  -- Specify the invariant which we want to hold true throughout the loop
  -- * `out` refers to the current value of the `let mut` variable
  -- * `xs` is a `List.Cursor`, which is a data structure representing
  --   a list that is split into a prefix `xs.prefix` and a suffix `xs.suffix`.
  --   It tracks how far into the loop we have gotten.
  -- Our invariant is that `out` holds the sum of the prefix.
  -- The notation ⌜p⌝ embeds a pure `p : Prop` into the assertion language.
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  -- After specifying the invariant, we can further simplify our goals by
  -- "leaving the proof mode". `mleave` is just `simp only [...] at *` with a stable simp subset.
  all_goals mleave
  -- Prove that our invariant is preserved at each step of the loop
  case vc1.step ih =>
    -- The goal here mentions `pref`, which binds the `prefix` field of the cursor passed to the
    -- invariant. Unpacking the (dependently-typed) cursor makes it easier for `grind`.
    grind
  -- Prove that the invariant is true at the start
  case _ =>
    grind
  -- Prove that the invariant at the end of the loop implies the property we wanted
  case vc3.a.post h =>
    grind

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

module

public import Std.Data.HashSet.Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

@[expose] def hnfWalk (m : Nat) (step : Nat → Array Nat → Array Nat) (key : Array Nat → Nat) :
    List (Nat × Nat) → List (Array Nat) → Std.HashSet Nat → Nat → Option Nat
  | [], _, _, cnt => some cnt
  | (up, g) :: rest, stack, seen, cnt =>
    if g < m then
      match stack.drop up with
      | [] => none
      | S :: tl =>
        let S' := step g S
        if seen.contains (key S') then none
        else hnfWalk m step key rest (S' :: S :: tl) (seen.insert (key S')) (cnt + 1)
    else none

end CFSG.EvenSporadicStandard.Solomon78

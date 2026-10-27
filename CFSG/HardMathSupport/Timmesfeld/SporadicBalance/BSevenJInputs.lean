module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElementsInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElementsInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

open CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native

@[expose] def b7JParse (s : String) : List (Nat × Bool) :=
  s.toList.filterMap fun c =>
    if c = 'a' then some (0, true) else if c = 'A' then some (0, false)
    else if c = 'b' then some (1, true) else if c = 'B' then some (1, false) else none

@[expose] def b7JUWord (_ : Unit := ()) : List (Nat × Bool) :=
  [(0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false)]

@[expose] def b7JEWord (_ : Unit := ()) : List (Nat × Bool) := b7JParse "abbaBabaBBaBabb"

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

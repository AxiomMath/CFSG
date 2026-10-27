module

public import CFSG.Sporadic.ONOddCore.SeedOrdersCheckInputs
public meta import CFSG.Sporadic.ONOddCore.SeedOrdersCheckInputs

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore

@[expose] def onWordO8 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 0, 3, 1, 3, 3, 1, 2]

@[expose] def onCodeTab (a ai b bi : Array Nat) (c : Nat) : Array Nat :=
  if c = 0 then a else if c = 1 then ai else if c = 2 then b else bi

@[expose] def onWordTab (a ai b bi : Array Nat) (w : List Nat) : Array Nat :=
  w.foldr (fun c acc => pcomp nPts (onCodeTab a ai b bi c) acc) (pid nPts)

@[noinline, expose] def onOrderEightOK (a b : Array Nat) : Bool :=
  let ai := pinvCand nPts a
  let bi := pinvCand nPts b
  let x := onWordTab a ai b bi onWordO8
  pisInv nPts a ai && pisInv nPts b bi &&
    peq nPts (ppow x 8) (pid nPts) && !peq nPts (ppow x 4) (pid nPts)

end CFSG.EvenSporadicStandard.Induction

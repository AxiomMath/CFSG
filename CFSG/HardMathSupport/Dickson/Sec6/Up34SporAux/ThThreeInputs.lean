module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenInputs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative

set_option compiler.extract_closed false

@[expose] def prog3 : List Op := [
  .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 2 6, .mul 6 3 7, .mul 2 7 8, .mul 8 3 9,
  .mul 2 6 7, .pow 5 7 1, .mul 2 9 4, .mul 4 3 5, .mul 8 5 6, .mul 5 8 7, .pow 27 6 5,
  .pow 7 7 6, .mul 5 6 7, .pow 35 7 6, .mul 6 0 4, .mul 4 7 0, .mul 3 8 4, .mul 4 2 5,
  .mul 9 5 6, .pow 10 6 7, .pow 38 7 6, .mul 6 1 4, .mul 4 7 1, .mul 0 1 10, .pow 13 10 11,
  .pow 3 10 12, .mul 12 1 13, .pow 2 13 14
  ]

@[expose] def n3 : Nat := 15

@[expose] def regs3 (_ : Unit := ()) : Array (Array V4) :=
  slpRows (rowsOf seedA) (rowsOf seedB) n3 prog3

@[expose] def ordOK (X : Array V4) (p : Nat) : Bool :=
  eqRows (powRowsN X p) idRows && rowsDiffer X idRows

@[expose] def commOK (X Y : Array V4) : Bool := eqRows (mulRows X Y) (mulRows Y X)

@[expose] def th3LocalOK (_ : Unit := ()) : Bool :=
  let R := regs3 ()
  prog3.all (Op.lt n3) && ordOK R[11]! 3 && ordOK R[14]! 7 && ordOK R[12]! 13 &&
    commOK R[11]! R[14]! && commOK R[11]! R[12]!

@[expose] def th3ScanOK (c : Nat) : Bool :=
  let R := regs3 ()
  centCheckMulti R[11]! 63685439 c 0 10000

end CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative

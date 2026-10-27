module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpInputs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.ThThirteenNative

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative

set_option compiler.extract_closed false

@[expose] def y13Word : List Int :=
  [
    1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1,
    -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2,
    1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2
  ]

@[expose] def g13Word : List Int :=
  [
    1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2,
    1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1,
    -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2,
    1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1,
    2, 1, 2, 1, -2, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2,
    1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1,
    -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1,
    2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1,
    -2, 1, 2, 1, 2, 1
  ]

@[expose] def y13Rows (_ : Unit := ()) : Array V4 := wordRows (xRows ()) (yRows ()) y13Word

@[expose] def g13Rows (_ : Unit := ()) : Array V4 := wordRows (xRows ()) (yRows ()) g13Word

@[expose] def th13OK (_ : Unit := ()) : Bool :=
  let Y := y13Rows ()
  let G := g13Rows ()
  eqRows (powRowsN Y 13) idRows && rowsDiffer Y idRows &&
    eqRows (mulRows Y G) (mulRows G (powRowsN Y 2))

end CFSG.HardMathSupport.Dickson.Sec6.I1431.ThThirteenNative

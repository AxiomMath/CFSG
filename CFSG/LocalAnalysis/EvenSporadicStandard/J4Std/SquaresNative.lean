module

public import CFSG.Sporadic.J4.QTNative

public section

namespace CFSG.EvenSporadicStandard.J4Std

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def sqWordB : List Int :=
  [-3, 1, 1, -3, 1, -2, 3, 1, -3, -3, 1, -2, 3, 1, -3, -3, 1, -2, 3, 1, -3, -1, -1, 3]

@[expose] def sqWordA : List Int :=
  [-3, -1, 2, 2, 3, 3, 3, -2, 3, 3, 3, -2, -2, -2, 1, 3]

@[expose] def chkSqRoot (loc inv : Array (Array V2)) (w : List Int) (c : Nat) : Bool :=
  let P := wordRows loc inv w
  eqRows (mulRows P P) (etaRows (uTab loc inv) 11 c)

@[expose] def chkSq (loc inv : Array (Array V2)) : Bool :=
  chkSqRoot loc inv sqWordB 1 && chkSqRoot loc inv sqWordA 3

end CFSG.EvenSporadicStandard.J4Std

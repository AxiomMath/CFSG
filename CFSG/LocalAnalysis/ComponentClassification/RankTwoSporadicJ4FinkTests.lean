module

public import CFSG.Sporadic.J4.QT2LocZNative
public import CFSG.Sporadic.J4.QT2LocCntNative
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkData

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J4Fink

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def z2Mask : Nat := 911

@[expose] def e0V : V2 := V2.ofFn fun j => j == 0

@[expose] def chkFinkC1 : Bool :=
  let u := etaRows (uTab (locMats ()) (locInvs ())) 11 z2Mask
  let y := mixRowsOf y7Word
  let p := mulRows u (mulRows (mulRows y u) (powRows y 6))
  eqRows (powRows p 4) idRows && differs (frApply (frTable (powRows p 2)) e0V) e0V

@[expose] def actWord (w : List Int) (c : Nat) : Nat := w.foldr act c

@[expose] def chkFinkC2 : Bool :=
  (c2Words.all fun w => w.all fun l => letters.contains l) &&
    (c2Words.all fun w => actWord w 1 == 1) &&
    (tMasks.filter (· != 1)).all fun v =>
      c2Words.any fun w => zMasks.contains (v ^^^ actWord w v)

end CFSG.ComponentClassification.RankTwoSporadic.J4Fink

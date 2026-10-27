module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3UData

public section

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.EvenSporadicStandard.M24Std.CU43

@[expose] def mulTab (j k : ℕ) : ℕ :=
  4 * (((j / 4) + (k / 4)) % 2) +
    ((((if k / 4 = 0 then j % 4 else (4 - j % 4) % 4)) + k % 4) % 4)

@[expose] def d8Check : Bool :=
  (List.range 8).all fun j => (List.range 8).all fun k =>
    eqA 820 (compA 820 (tArr j) (tArr k)) (tArr (mulTab j k))

@[expose] def rhoCosetCheck : Bool :=
  eqA 820 (compA 820 rhoArr rhoArr) (idA 820) &&
    inP (compA 820 rhoArr (invCand 820 (tArr 5)))

end CFSG.EvenSporadicStandard.Fin76b.U16

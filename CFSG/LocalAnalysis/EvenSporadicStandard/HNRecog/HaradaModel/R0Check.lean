module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.AData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def bilC (x y : ℕ) : ℕ :=
  (bitOf x 0 * bitOf y 1 + bitOf x 1 * bitOf y 0 + bitOf x 2 * bitOf y 3 + bitOf x 3 * bitOf y 2 +
    bitOf x 4 * bitOf y 5 + bitOf x 5 * bitOf y 4) % 2

@[expose] def eichC (w u x : ℕ) : ℕ :=
  x ^^^ (if bilC x w == 1 then u else 0) ^^^
    (if (bilC x u + qmC u * bilC x w) % 2 == 1 then w else 0)

@[expose] def etaCodes : List ℕ := (List.range 64).filter fun u => bilC u 1 == 0 && lamC u == 0

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel

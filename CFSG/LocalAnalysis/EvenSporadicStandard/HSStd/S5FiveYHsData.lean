module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYLin
public import CFSG.RankThree.Native.HSMcLSmallData

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def hsGens : Array (Array ℕ) := #[hs100Arr 0, hs100Arr 1, hs100Arr 15]

@[expose] def x3 : Array ℕ :=
  compA 100 (compA 100 (hs100Arr 0) (hs100Arr 15)) (compA 100 (hs100Arr 0) (hs100Arr 15))

@[expose] def x3OK : Bool :=
  allLt hsGens.size (fun k => validA 100 hsGens[k]!) && validA 100 x3 &&
    eqA 100 (compA 100 x3 (compA 100 x3 x3)) (idA 100) && !eqA 100 x3 (idA 100)

end CFSG.EvenSporadicStandard.HSStd.FiveY

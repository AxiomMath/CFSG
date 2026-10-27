module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYLin
public import CFSG.RankThree.Native.HSMcLSmallData

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def hsGens : Array (Array ℕ) := #[hs100Arr 0, hs100Arr 1, hs100Arr 15]

@[expose] def hsKeys : List ℕ := [0, 1, 2, 3, 4]

@[expose] def x3 : Array ℕ :=
  compA 100 (compA 100 (hs100Arr 0) (hs100Arr 15)) (compA 100 (hs100Arr 0) (hs100Arr 15))

@[expose] def hsAct (k : ℕ) (a : Array ℕ) : Array ℕ := conjA 100 hsGens[k]! a

@[expose] def x3Cert : ArrCert := arrBfs hsAct hsGens.size (keyA 100 hsKeys) x3 130000

@[expose] def x3OK : Bool :=
  allLt hsGens.size (fun k => validA 100 hsGens[k]!) && validA 100 x3 &&
    eqA 100 (compA 100 x3 (compA 100 x3 x3)) (idA 100) && !eqA 100 x3 (idA 100) &&
    arrCertOKL hsAct hsGens.size (validA 100) (keyA 100 hsKeys) x3 x3Cert &&
    x3Cert.pts.size == 123200

end CFSG.EvenSporadicStandard.HSStd.FiveY

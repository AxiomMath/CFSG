module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYLin

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.EvenSmallLie.Child3.SelL39

@[expose] def tKeys : List ℕ := [0, 1, 2, 9, 10]

@[expose] def uWords : List (List ℤ) :=
  [[-1, -1, -1, -1, 2, -1, -2, -2, -2, -1, -2, -2, 1, 2, 1, -2, -2, 1, -2, -1, -2, 1, 2, 1, 2, -1,
    -2, -1, -1, 2, 2, 2, -1, -2, -2, -1, -1, 2, 1],
   [1, 1, -2, 1, -2, 1, 1, 2, 2, -1, 2, -1, -2, 1, -2, -1, -2, 1, 2, 1, 2, -1, -1, -1, 2, 1, -2, -1,
    -2, 1, 1, 1, -2, -2, 1, 1, 1],
   [1, 1, -2, 1, -2, 1, 1, 2, 2, -1, 2, 1, 2, 1, -2, 1, -2, 1, 1, -2, -1, 2, 2, 2, 2, 1, -2, -2, 1,
    2],
   [-1, -2, -2, 1, 2, 1, -2, -2, -2, -1, -2, -1, 2, -1, -2, -1, 2, 2, 1, 2, 2, 2, 1, -2, -1, -1,
    -1, -1, -1, -2, 1, 1, 1, 2, -1, -2, -2, 1, 1, 1, -2, -1, -2, -1, 2, 2, 1, 1, -2, -1, -2, 1, -2,
    -1],
   [-1, -2, 1, 1, 2, 2, -1, 2, 1, 2, 1, -2, -2, -1, 2, -1, -2, -1, 2, 2, 1, 2, 2, 2, 1, 1, -2, -1,
    -1, -1, 2, 2, 1, -2, -1, -1, -2, 1, -2, -2, -1, -1, 2, -1, 2, -1, -1],
   [-2, -1, 2, 2, 2, 2, 1, 2, -1, 2, 2, 2, 2, 2, 1, 2, 2, 1, -2, 1, 2, -1, -2, -2, 1, 1, -2, -1, 2,
    1, 1, 1, 1, -2, 1, 2, 2, -1, -2, -2, -1, -2, -2, -2, -2, -1]]

@[expose] def uGens : Array (Array ℕ) := (uWords.map tW).toArray

@[expose] def uCert : ArrCert := enumBfs 182 uGens tKeys 800

@[expose] def fixCount (a : Array ℕ) : ℕ :=
  ((Finset.range 182).filter fun p => a[p]! = p).card

@[expose] def g7 : Array ℕ := tW [1, 2, 1, 1]

@[expose] def u3OK : Bool :=
  enumOKL 182 uGens tKeys uCert && uCert.pts.size == 729 &&
    uCert.pts.toList.all (fun a => eqA 182 a (idA 182) || fixCount a == 2 || fixCount a == 20) &&
    validA 182 g7 &&
    eqA 182 (compA 182 g7 (compA 182 g7 (compA 182 g7 (compA 182 g7
      (compA 182 g7 (compA 182 g7 g7)))))) (idA 182) && fixCount g7 == 0

end CFSG.EvenSporadicStandard.HSStd.PumpTC7

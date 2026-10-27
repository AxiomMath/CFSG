module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSData
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.PairHSCheckInputs

public noncomputable section

namespace CFSG.QuasithinUnique.Id2519.UHS
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

@[expose] def letterArr (l : ℕ) : Array ℕ :=
  if l = 0 then PairHS.gens[0]! else if l = 1 then PairHS.gens[1]! else PairHS.gensInv[1]!

@[expose] def wArr (ws : List ℕ) : List (Array ℕ) := (ws.map letterArr).reverse

@[expose] def cLetters : List ℕ := (List.replicate 5 [0, 1, 1]).flatten

@[expose] def nodeWordFuel : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, k =>
    if k = 0 then [] else
      nodeWordFuel fuel nodePar[k]! ++ (if nodeLab[k]! = 0 then y1Letters else y2Letters)

@[expose] def nodeWord (k : ℕ) : List ℕ := nodeWordFuel 360 k

@[expose] def a6Check : Bool :=
  ordB PairHS.bs (wArr y1Letters) 3 && ordB PairHS.bs (wArr y2Letters) 5 &&
  (baseImgs PairHS.bs (wArr (y1Letters ++ cLetters)) ==
    baseImgs PairHS.bs (wArr (cLetters ++ y1Letters))) &&
  (baseImgs PairHS.bs (wArr (y2Letters ++ cLetters)) ==
    baseImgs PairHS.bs (wArr (cLetters ++ y2Letters))) &&
  decide (nodePar.size = 360) && decide (nodeLab.size = 360) &&
  strictInc ((List.range 360).map fun k =>
    imgKey 3850 (baseImgs PairHS.bs (wArr (nodeWord k)))).mergeSort &&
  (List.range 360).all fun k =>
    !ordB PairHS.bs (wArr (nodeWord k)) 2 ||
      (baseImgs PairHS.bs (wArr (conjWords[k]! ++ cLetters)) ==
        baseImgs PairHS.bs (wArr (cLetters ++ nodeWord k ++ conjWords[k]!)))

end CFSG.QuasithinUnique.Id2519.UHS

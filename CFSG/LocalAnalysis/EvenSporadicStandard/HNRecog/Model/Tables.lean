module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Data

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.HSMultiplier
open CFSG.EvenSporadicStandard.TwoHS

@[expose] def h1408Hex : String := include_str "H1408Tbl.txt"

@[expose] def h1408T (j : ℕ) : Table := hexT 3 1408 (1408 * j) h1408Hex

@[expose] def h1408X (i : Fin 6) : Table := h1408T i.val

@[expose] def h1408XI (i : Fin 6) : Table := invT 1408 (h1408X i)

@[expose] def h1408Xs : List Table := (List.finRange 6).map h1408X

@[expose] def h1408V : Table := h1408T 6

@[expose] def h1408R25 : List (Fin 6 × Bool) := hsRels.getD 24 []

@[expose] def h1408T25 : Table := evalW 1408 h1408X h1408XI h1408R25

@[expose] def h1408PermOK : Bool :=
  (List.finRange 6).all (fun i => permOK 1408 (h1408X i) && invOK 1408 (h1408X i) (h1408XI i)) &&
    permOK 1408 h1408V && invoOK 1408 h1408V

@[expose] def h1408RelOK : Bool :=
  hsRels.all (fun r => (List.finRange 6).all fun i =>
    commTT 1408 (h1408X i) (evalW 1408 h1408X h1408XI r)) &&
  (List.finRange 6).all (fun i =>
    tblEq 1408 (evalW 1408 h1408X h1408XI (hsCommWord i)) (h1408X i))

@[expose] def h1408SigmaOK : Bool :=
  (List.finRange 6).all (fun i =>
    tblEq 1408 (conjT 1408 h1408V h1408V (h1408X i))
      (wordTbl 1408 h1408Xs (sigWords.getD i.val [])))

@[expose] def h1408CentralOK : Bool :=
  involOK 1408 h1408T25 && (List.range 1408).all fun p => ap h1408T25 p != p

@[expose] def h1408BlockOK : Bool :=
  (List.finRange 6).all (fun i =>
    (List.range 704).all (fun k => decide (ap (h1408X i) k < 704)) &&
    (List.range 704).all (fun k => decide (704 ≤ ap (h1408X i) (704 + k)))) &&
  (List.range 704).all (fun k => ap h1408V k == 704 + k && ap h1408V (704 + k) == k)

end CFSG.EvenSporadicStandard.HNRecog

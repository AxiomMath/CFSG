module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native

@[expose] def hnsBase (r : Fin 4) : ℕ := [6, 13, 22, 35].getD r.val 0

@[expose] def hnsNum (r : Fin 4) : ℕ := [2, 4, 4, 4].getD r.val 0

@[expose] def hnsGen (r i : Fin 4) : Table := hsCentTbl (hnsBase r + i.val)

@[expose] def hnsGenI (r i : Fin 4) : Table := invT 3850 (hnsGen r i)

@[expose] def hnsWordsA : List (List (Fin 4 × Bool)) :=
  [[(1, true), (0, false), (1, true), (0, true), (1, false), (0, true), (1, true)],
    [(0, true), (2, true), (0, true), (2, true)],
    [(0, false), (3, false)],
    [(0, false), (2, true), (2, true)]]

@[expose] def hnsWordsB : List (List (Fin 4 × Bool)) :=
  [[(0, true), (1, false), (1, false)],
    [(1, false), (0, true)],
    [(2, false), (1, true), (3, false), (1, false)],
    [(1, true), (1, true)]]

@[expose] def hnsWordA (r : Fin 4) : List (Fin 4 × Bool) := hnsWordsA.getD r.val []

@[expose] def hnsWordB (r : Fin 4) : List (Fin 4 × Bool) := hnsWordsB.getD r.val []

@[expose] def hnsA (r : Fin 4) : Table := evalW 3850 (hnsGen r) (hnsGenI r) (hnsWordA r)

@[expose] def hnsB (r : Fin 4) : Table := evalW 3850 (hnsGen r) (hnsGenI r) (hnsWordB r)

@[expose] def hnsCheck (r : Fin 4) : Bool :=
  (hnsWordA r).all (fun l => decide (l.1.val < hnsNum r)) &&
    (hnsWordB r).all (fun l => decide (l.1.val < hnsNum r)) &&
    (List.finRange 4).all
      (fun i => permOK 3850 (hnsGen r i) && invOK 3850 (hnsGen r i) (hnsGenI r i)) &&
    ordTest 3850 2 (hnsA r) && ordTest 3850 3 (hnsB r) &&
    ordTest 3850 5 (compT 3850 (hnsA r) (hnsB r))

@[expose] def hnsOK : Bool := (List.finRange 4).all hnsCheck

end CFSG.EvenSporadicStandard.TwoHS

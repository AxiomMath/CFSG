module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs

public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.RuSchreier

@[expose] def lettersOK (k : ℕ) (w : List ℤ) : Bool := w.all fun z => z != 0 && decide (z.natAbs ≤ k)

@[expose] def basePtOK (n : ℕ) (hT hTi : Array Table)
    (q : ℕ × List (List ℤ) × List (ℕ × List ℤ)) : Bool :=
  let sT := q.2.1.map (wordT n (letterTab hT hTi))
  decide (q.1 < n) && q.2.1.all (lettersOK hT.size) && q.2.2.all (fun f => lettersOK hT.size f.2) &&
    sT.all (fun s => ap s q.1 == q.1) &&
    allIn 0 n (fun i => !(sT.all fun s => ap s i == i) || q.2.2.any (fun f => f.1 == i)) &&
    q.2.2.all fun f =>
      ap (wordT n (letterTab hT hTi) f.2) q.1 == f.1 && ap (wordT n (letterTab hT hTi) f.2) f.1 == q.1

@[expose] def fourBaseOK (n : ℕ) (gens : Array Table) (hw : List (List ℤ)) (p : ℕ)
    (pts : List (ℕ × List (List ℤ) × List (ℕ × List ℤ))) : Bool :=
  let gi := gens.map (invT n)
  let hT := (hw.map (wordT n (letterTab gens gi))).toArray
  let hTi := hT.map (invT n)
  gens.all (fun g => invOK n g (invT n g)) && hw.all (lettersOK gens.size) &&
    (List.range hT.size).all (fun i => invOK n hT[i]! hTi[i]! &&
      tblEq n (wordT n (letterTab hT hTi) (List.replicate p ((i : ℤ) + 1))) (idT n)) &&
    pts.all (basePtOK n hT hTi)

@[expose] def baseGensC : Array Table := #[tblOfArr (ruField4060 1)[0]!, tblOfArr (ruField4060 1)[1]!]

@[expose] def baseGensL : Array Table :=
  #[tblOfArr (ruField4060 5)[0]!, tblOfArr (ruField4060 5)[1]!, tblOfArr (ruField4060 5)[2]!]

@[expose] def fourHC : List (List ℤ) :=
  [[1, 1, 1, 1], [-1, -1, -1, -1], [2, 1, 1, -2, 2, 1, 1, -2]]

@[expose] def fourPtsC : List (ℕ × List (List ℤ) × List (ℕ × List ℤ)) :=
  [(0,
    [[-3, 1, 1, 3, 3, -2, -1, 2, 1, -3, -3, 1, -2, 2, -2, -2, 3],
     [-1, -3, -1, -3, -3, 1, 3, 1, 3, 3, 3, 2, 3, -2, 1, -3, 1, 3, 2],
     [-1, 3, 3, -1, -1, -3, 3, -2, 3, 3, 2, -3, -1, -1, 2, 2, -2, 1]],
    [(0, []), (921, [3, 3, 1, 3, -1, -3, -3, -1])]),
   (1,
    [[-3, 1, -3, -3, 1, -3, -3, -1, 1, -2, 1, 3, -2, -2, -1, 1, 2, -3],
     [-1, -3, -1, -3, -3, 1, 3, 3, 1, -1, 3, -1, -1, 2, -2, 3, 2]],
    [(1, []), (2243, [3, 1, -3, 1, 3, 1, 1])]),
   (2,
    [[3, 3, 1, -3, 1, 3, -3, -2, -1, 2, -1, -2, 2, 1, 3, 2, -3, -3],
     [-1, -3, -1, -3, -3, 1, 1, -3, -2, 1, 3, -2, -3, 2, 2, 3, -2, 3, 2],
     [-1, -1, -3, -1, -3, 1, -2, 2, 1, 1, 3, -2, -2, 1, 1, 3, 2, -3],
     [1, -3, -1, -1, -3, -1, -1, -1, 3, -2, 2, -3, 3, -1, 3, 3, -3, 3]],
    [(2, []), (1264, [-3, 1, 3, 1, -3, 1, 3, 1])])]

@[expose] def fourHL : List (List ℤ) := [[1, 2, 1, 2], [1, 3, 1, 3]]

@[expose] def fourPtsL : List (ℕ × List (List ℤ) × List (ℕ × List ℤ)) :=
  [(0,
    [[2, 2, 2, -1, -1, -2, 1, 1, 1, 1, -1, -1, 2, 1, -2, -1, -2],
     [-1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, -2, -1, -1, 1, -2, -1, -2, -1]],
    [(0, []), (1, [2, 1, -2, -2, -2, -1, -2, -1]), (3645, [-2, 1, -2, 1, 1, -2, -1, -1]),
     (3692, [-2, -2, -1, -2, 1, -2, 1, 1])]),
   (2,
    [[-1, -1, 2, -2, -1, -1, -2, 2, -2, -1, -1, -1, -1, -2, 2],
     [-1, 2, -1, 2, 2, -1, -2, 2, 1, -1, 1, 2, -1, -2, -1, -1],
     [2, 2, 2, 1, -1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, -2]],
    [(2, []), (4, [2, 2, 2, 2, 1, 2, 1, 1, 2]), (2137, [-2, -1, 2, 1, -2, -2, 1, 1, 1]),
     (2665, [-2, -2, -1, -1, 2, 1, 1])])]

@[expose] def fourBaseC : Bool := fourBaseOK 4060 baseGensC fourHC 5 fourPtsC

@[expose] def fourBaseL : Bool := fourBaseOK 4060 baseGensL fourHL 13 fourPtsL

end CFSG.EvenSporadicStandard.TwoRu.HypOne

module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8Defs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridgeData
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.HeldB.Common
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcO8E

open CFSG.ComponentClassification.RankTwoClassical.ExcO8
open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

@[expose] def pairA (t u : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 480) fun j => if j.val < 240 then t[j.val]! else u[j.val - 240]! + 240

@[expose] def eArrs : Array (Array ℕ) :=
  ((List.range 8).map fun i =>
    pairA (wordArr (omWords.getD (rhoPerm.getD i 0) [])) (wordArr (omWords.getD i []))).toArray

@[expose] def eGens : List (Equiv.Perm (Fin 480)) :=
  (List.range 8).map fun i => permOrId 480 eArrs[i]!

@[expose] def okW (_ : List ℤ) : Bool := true

@[expose] def z1 : Equiv.Perm (Fin 480) := permOrId 480 (pairA negArr (idA 240))

@[expose] def z2 : Equiv.Perm (Fin 480) := permOrId 480 (pairA (idA 240) negArr)

@[expose] def z3 : Equiv.Perm (Fin 480) := permOrId 480 (pairA negArr negArr)

@[expose] def zs : List (Equiv.Perm (Fin 480)) := [z1, z2, z3]

@[expose] def seGens : List (Equiv.Perm (Fin 480)) :=
  [[1], [3], [5], [7]].map fun w => tab (evalCodes eGens w)

@[expose] def seQ : RawSchreierDatum 480 :=
  certificate (by decide) seGens
    [[2, 1, 2], [2, 3, 2], [4, 1, 4, 2], [3, 1], [3, 1, 3, 1]]
    #v[0, 1, 4, 240] (by decide)

@[expose] def seRepWords : List (List ℤ) :=
  [[1], [2], [3], [4], [4, 3, 1], [2, 1, 2, 1], [3, 1, 3, 1], [4, 1, 4, 1], [3, 2, 3, 2],
    [4, 2, 4, 2], [4, 3, 4, 3], [2, 3, 2, 1, 2, 3, 2, 1], [2, 4, 2, 1, 2, 4, 2, 1],
    [4, 2, 3, 2, 4, 2, 3, 2], [4, 2, 4, 3, 2, 3, 1, 2, 1], [4, 2, 4, 3, 2, 3, 2, 1, 2, 1],
    [4, 2, 3, 2, 4, 2, 1, 2, 3, 2, 1], [2, 4, 3, 2, 1, 2, 4, 2, 3, 2, 1],
    [2, 4, 2, 3, 1, 2, 4, 2, 3, 2, 1], [4, 2, 3, 1, 2, 4, 1, 2, 3, 1, 2, 1],
    [4, 3, 2, 3, 1, 2, 4, 2, 3, 1, 2, 1], [4, 2, 3, 2, 4, 1, 2, 4, 3, 1, 2, 1],
    [4, 3, 2, 4, 3, 2, 1, 2, 4, 3, 2, 1], [4, 2, 3, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 1],
    [4, 2, 3, 2, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1], [4, 2, 1, 2, 3, 2, 4, 1, 2, 3, 2, 1, 2, 1],
    [4, 3, 2, 4, 3, 1, 2, 4, 3, 1, 2, 4, 3, 1, 2, 1],
    [2, 4, 2, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 3, 2, 1]]

@[expose] def seReps : List (Equiv.Perm (Fin 480)) :=
  seRepWords.map fun w => tab (evalCodes seGens w)

@[expose] def fusion : List (ℕ × List ℤ) :=
  [(1, [-4, -3, -6, -5, -8, -4, -7, -3]), (1, [-4, -2, -3, -1, -6, -5, -8, -7]),
    (1, [-4, -2, -3, -1, -8, -4, -7, -3]), (1, [-4, -2, -3, -1, -6, -4, -5, -3]),
    (2, [-2, -1, -3, -6, -5, -8, -4, -7, -3]), (1, [-1, -4, -3, -6, -5, -8, -7]), (0, []), (0, []),
    (1, [-4, -2, -5, -3, -1, -8, -7]), (1, [-4, -2, -6, -7, -3, -1, -5]), (0, []),
    (1, [-4, -5, -3, -8, -7]), (1, [-4, -6, -7, -3, -5]), (1, [-4, -2, -5, -3, -1]),
    (2, [-2, -1, -3, -5, -6, -8, -7, -3, -5]), (2, [-2, -1, -3, -6, -5, -8, -7]),
    (2, [-2, -1, -3, -8, -7]), (2, [-1, -6, -8, -7, -3, -1, -3]),
    (2, [-1, -6, -5, -3, -1, -2, -7]), (2, []), (2, [-3, -5, -7, -8, -4, -3]),
    (2, [-1, -6, -4, -3, -1, -7, -3]), (2, [-2, -3, -4, -5, -7, -3, -4]), (2, [-3, -8]), (2, [-2]),
    (2, [-3, -1, -5, -3, -6]), (1, []), (1, [-4, -5])]

@[expose] def x48 : Equiv.Perm (Fin 480) :=
  tab (evalCodes seGens [4, 3, 2, 4, 3, 1, 2, 4, 3, 1, 2, 4, 3, 1, 2, 1])

@[expose] def x16 : Equiv.Perm (Fin 480) :=
  tab (evalCodes seGens [4, 2, 3, 1, 2, 4, 1, 2, 3, 1, 2, 1])

@[expose] def xs : List (Equiv.Perm (Fin 480)) := [x48, x16]

@[expose] def xsFix : List ℕ := [48, 16]

@[expose] def xsMin : List ℕ := [4, 16]

@[expose] def s48Words : List (List ℤ) :=
  [[2], [1, 2, 1], [4, 3, 1], [4, 1, 3], [3, 2, 3], [4, 2, 4]]

@[expose] def s48Gens : List (Equiv.Perm (Fin 480)) :=
  s48Words.map fun w => tab (evalCodes seGens w)

@[expose] def s48Q : RawSchreierDatum 480 :=
  certificate (by decide) s48Gens
    [[2, 1], [5, 1], [6, 2, 6], [3, 6, 3, 1], [4, 3]]
    #v[0, 1, 240] (by decide)

@[expose] def r48Words : List (List ℤ) :=
  [[1], [2], [3], [5], [6], [2, 1], [5, 1], [6, 1], [4, 3], [6, 5, 2], [6, 5, 2, 1],
    [3, 5, 3, 2], [3, 6, 3, 2], [6, 2, 6, 2], [6, 3, 5, 3], [6, 5, 6, 5], [3, 5, 2, 3, 1],
    [3, 6, 2, 3, 1], [3, 6, 5, 3, 1], [6, 3, 5, 3, 2, 1], [3, 6, 5, 3, 2, 1], [5, 3, 6, 3, 2, 1],
    [6, 5, 3, 2, 3, 1], [6, 3, 5, 2, 3, 1], [3, 6, 5, 2, 3, 1], [5, 3, 6, 2, 3, 1],
    [5, 3, 2, 1, 3, 2, 1], [6, 3, 2, 1, 3, 2, 1], [5, 3, 5, 1, 3, 2, 1], [6, 3, 6, 1, 3, 2, 1],
    [5, 3, 5, 2, 3, 2, 1], [6, 3, 6, 2, 3, 2, 1], [6, 5, 3, 5, 1, 3, 1], [6, 3, 6, 5, 1, 3, 1],
    [6, 5, 3, 6, 5, 3, 1], [6, 5, 3, 5, 2, 3, 2], [6, 3, 6, 5, 2, 3, 2], [6, 5, 3, 6, 5, 3, 2],
    [6, 5, 3, 2, 1, 3, 2, 1], [6, 5, 3, 5, 1, 3, 2, 1], [6, 5, 3, 6, 1, 3, 2, 1],
    [5, 3, 6, 5, 2, 3, 2, 1], [6, 3, 6, 5, 2, 3, 2, 1], [3, 1, 3, 1, 3, 1, 3, 1],
    [4, 1, 3, 1, 3, 1, 3, 1], [6, 5, 3, 6, 5, 2, 3, 1], [3, 2, 3, 2, 3, 2, 3, 2],
    [4, 2, 3, 2, 3, 2, 3, 2], [6, 5, 3, 6, 5, 2, 1, 3, 2, 1]]

@[expose] def r48Reps : List (Equiv.Perm (Fin 480)) := r48Words.map (evalCodes s48Gens)

@[expose] def d48Data : String :=
  "1:7,5,1:1|1:7,5,1:1|1:3:1|1:1,3,1:1|1:1,3,1:1|1:7,5,1:1|1:1,3,1:1|1:1,3,1:1||1:1,3,1:1|1:1,3,1:\
  1|1:3:1|1:3:1||1:3:1||1:3:1|1:3:1|1:3:1|1:3:1|1:3:1|1:3:1|1:3:1|1:3:1|1:1,3,1:1|1:3:1|1:3:1|1:3:\
  1|1:3:1|1:3:1|1:3:1|1:3:1|1:3:1|1:3:1|1:3:1|1:3:1|1:1,3,1:1|1:3:1|1:3:1|1:3:1|1:3:1|1:1,3,1:1|1:\
  1,3,1:1|||1:7,5,1:1|||1:1,3,1:1"

@[expose] def d48 : List (List (ℕ × List ℤ × ℕ)) := parseDerivs d48Data

@[expose] def s16Words : List (List ℤ) :=
  [[3, 1], [4, 1], [1, 2, 1], [2, 4, 3, 1, 2, 4, 3, 1, 2], [2, 3, 1, 2, 4, 1, 2, 3, 1, 2]]

@[expose] def s16Gens : List (Equiv.Perm (Fin 480)) :=
  s16Words.map fun w => tab (evalCodes seGens w)

@[expose] def s16Q : RawSchreierDatum 480 :=
  certificate (by decide) s16Gens
    [[3, 2, 2], [1, 1]]
    #v[0, 1, 4, 240] (by decide)

@[expose] def r16Words : List (List ℤ) :=
  [[3], [1, 1], [2, 2], [5, 2], [2, 2, 1, 1], [4, 3, 2, 1], [5, 4, 3, 2], [3, 5, 3, 2],
    [4, 5, 3, 2], [4, 1, 3, 2, 1], [4, 2, 3, 2, 1], [4, 5, 3, 2, 1], [4, 3, 1, 3, 1],
    [5, 3, 2, 3, 2], [4, 2, 1, 3, 2, 1], [3, 5, 2, 3, 2, 1], [4, 3, 1, 4, 3, 1],
    [3, 4, 1, 4, 3, 1], [4, 3, 5, 4, 3, 2], [4, 3, 1, 4, 3, 1, 1, 1], [3, 4, 1, 4, 3, 1, 1, 1],
    [3, 2, 4, 3, 1, 3, 2, 1]]

@[expose] def r16Reps : List (Equiv.Perm (Fin 480)) := r16Words.map (evalCodes s16Gens)

@[expose] def d16Data : String :=
  "|||||1:5,1:1|1:5,1:1|1:1,3,1:1|1:5,1:1|1:1,3,1:1|1:7,1:1|1:5,1:1||1:5,1:1||1:5,1:1||||||"

@[expose] def d16 : List (List (ℕ × List ℤ × ℕ)) := parseDerivs d16Data

@[expose] def censusArrCheck : Bool :=
  (List.range 8).all (fun i => isInvA 480 eArrs[i]! (invCand 480 eArrs[i]!) &&
      isInvA 480 (invCand 480 eArrs[i]!) eArrs[i]!) &&
    [pairA negArr (idA 240), pairA (idA 240) negArr, pairA negArr negArr].all (fun t =>
      isInvA 480 t (invCand 480 t) && isInvA 480 (invCand 480 t) t) &&
    schreierPermEq (evalCodes eGens [1, 5, 1, 5]) z2 &&
    schreierPermEq (evalCodes eGens [5, 7, 5, 7]) z1

@[expose] def censusChainCheck : Bool :=
  seQ.check && seQ.orderCertificate == 16384 &&
    s48Q.check && s48Q.orderCertificate == 4096 &&
    s48Gens.all (fun g => schreierPermEq (g * x48) (x48 * g)) &&
    s16Q.check && s16Q.orderCertificate == 1024 &&
    s16Gens.all (fun g => schreierPermEq (g * x16) (x16 * g))

@[expose] def censusCoverCheck : Bool :=
  repsOK 480 (listTables seGens) (listTables (seGens.map (·⁻¹))) (cosetOrderTables seQ 1 2)
      (seReps.map toTable) 600 &&
    (seReps.map toTable).all (ordTest 480 2) &&
    repsOK 480 (listTables s48Gens) (listTables (s48Gens.map (·⁻¹)))
      (cosetOrderTables s48Q 1 2) (r48Reps.map toTable) 600 &&
    (r48Reps.map toTable).all (ordTest 480 2) &&
    repsOK 480 (listTables s16Gens) (listTables (s16Gens.map (·⁻¹)))
      (cosetOrderTables s16Q 1 2) (r16Reps.map toTable) 600 &&
    (r16Reps.map toTable).all (ordTest 480 2)

@[expose] def censusFusionCheck : Bool :=
  fusion.length == seReps.length && xs.map fixNum == xsFix &&
    xs.all (fun x => ordTest 480 2 (toTable x) && !zs.any (schreierPermEq x)) &&
    (seReps.zip fusion).all (fun p =>
      if p.2.1 = 0 then zs.any (schreierPermEq p.1)
      else
        let g := tab (evalCodes eGens p.2.2)
        decide (p.2.1 ≤ xs.length) &&
          schreierPermEq (g * p.1 * g⁻¹) (xs.getD (p.2.1 - 1) 1)) &&
    (seReps.zip (repSizes 480 (listTables seGens) (listTables (seGens.map (·⁻¹)))
      (seReps.map toTable) 600)).all (fun p =>
      (xsFix.zip xsMin).all fun q => fixNum p.1 != q.1 || decide (q.2 ≤ p.2))

@[expose] def censusDerivCheck : Bool :=
  d48.length == r48Reps.length && d16.length == r16Reps.length &&
    (r48Reps.zip d48).all (fun p =>
      schreierPermEq p.1 x48 || derivCheck eGens okW zs [] [x48, p.1] p.2) &&
    (r16Reps.zip d16).all (fun p =>
      schreierPermEq p.1 x16 || derivCheck eGens okW zs [48] [x16, p.1] p.2)

end CFSG.ComponentClassification.RankTwoClassical.ExcO8E

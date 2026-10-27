module

public import CFSG.Sporadic.Schreier.Co3Outer
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.HeldB.Common
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.Sporadic.Schreier.Co3Cert

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcSp6

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Certificates
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native

@[expose] def mGens : List (Equiv.Perm (Fin 276)) :=
  (List.range 7).map fun k => permOrId 276 co3MArrs[k]!

@[expose] def tGens : List (Equiv.Perm (Fin 276)) :=
  (List.range 8).map fun k => permOrId 276 co3TArrs[k]!

@[expose] def zC : Equiv.Perm (Fin 276) := permOrId 276 co3ZArr

@[expose] def tQ : RawSchreierDatum 276 :=
  certificate (by decide) tGens [[-6, 7], [-9, -2, -3, 1, 7, 3]] #v[0, 1, 2] (by decide)

@[expose] def xa : Equiv.Perm (Fin 276) := tab (evalCodes tGens [3, 1, 3, 2])

@[expose] def xb : Equiv.Perm (Fin 276) := tab (evalCodes tGens [1, 5])

@[expose] def fixCount (g : Equiv.Perm (Fin 276)) : ℕ :=
  (List.finRange 276).countP fun i => decide (g i = i)

@[expose] def tRepWords : List (List ℤ) :=
  [[3], [5], [7], [8], [1, 1], [1, 5], [1, 8], [2, 5], [2, 7], [4, 1], [4, 2], [1, 3, 5], [2, 7, 1],
    [3, 1, 6], [4, 1, 2], [3, 1, 3, 2], [3, 1, 6, 1]]

@[expose] def tReps : List (Equiv.Perm (Fin 276)) := tRepWords.map fun w => tab (evalCodes tGens w)

@[expose] def fusion : List (ℕ × List ℤ) :=
  [(1, [-4, -7]), (2, [-6, -4, -4, -4, -6, -3]), (1, [-2, -3, -5, -6, -3]),
    (1, [-2, -7, -2, -6, -5]), (0, []), (2, []), (2, [-6, -2, -3, -6]), (2, [-6, -2, -4, -6, -4]),
    (2, [-3, -7, -2, -5, -7]), (1, [-3, -6, -3, -4, -7]), (2, [-6, -6, -6, -5, -6]),
    (2, [-3, -7, -5, -3, -5, -4]), (2, [-3, -4, -6, -7, -7]), (2, [-3, -7, -6, -2, -7, -7]),
    (2, [-3, -6, -2, -4, -6, -6]), (1, []), (1, [-5, -5])]

@[expose] def saWords : List (List ℤ) :=
  [[1], [7], [2], [4], [8], [6, 3], [5, 6]]

@[expose] def saGens : List (Equiv.Perm (Fin 276)) := saWords.map fun w => tab (evalCodes tGens w)

@[expose] def saQ : RawSchreierDatum 276 :=
  certificate (by decide) saGens [[5], [-4, -5, 6, 4, 2, 6]] #v[0, 1] (by decide)

@[expose] def sbWords : List (List ℤ) :=
  [[6], [2], [3], [1, 5], [5, 4]]

@[expose] def sbGens : List (Equiv.Perm (Fin 276)) := sbWords.map fun w => tab (evalCodes tGens w)

@[expose] def sbQ : RawSchreierDatum 276 :=
  certificate (by decide) sbGens [[-4, 2, 2, 4, 1]] #v[0, 2] (by decide)

@[expose] def raWords : List (List ℤ) :=
  [[2], [5], [1, 1], [1, 5], [1, 7], [2, 3], [2, 4], [3, 5], [4, 1], [4, 3], [6, 1], [1, 5, 2],
    [2, 3, 1], [4, 1, 3], [6, 1, 3], [2, 7, 7, 5], [3, 7, 7, 1], [7, 7, 3, 1]]

@[expose] def raReps : List (Equiv.Perm (Fin 276)) := raWords.map (evalCodes saGens)

@[expose] def rbWords : List (List ℤ) :=
  [[1], [4], [5], [2, 2], [2, 5], [4, 1], [5, 4], [1, 2, 3], [2, 5, 4], [3, 5, 1], [4, 2, 2],
    [2, 3, 2, 1], [3, 5, 4, 1], [4, 1, 2, 3], [4, 2, 3, 2, 1]]

@[expose] def rbReps : List (Equiv.Perm (Fin 276)) := rbWords.map (evalCodes sbGens)

@[expose] def maskProd : List (Equiv.Perm (Fin 276)) → ℕ → Equiv.Perm (Fin 276)
  | [], _ => 1
  | g :: gs, m => (if m % 2 = 1 then g else 1) * maskProd gs (m / 2)

@[expose] def badState (forbid : List ℕ) (cur : List (Equiv.Perm (Fin 276))) : Bool :=
  cur.any (fun g => !schreierPermEq (g * g) 1) ||
    cur.any (fun g => cur.any fun h => !schreierPermEq (g * h) (h * g)) ||
    (List.range (2 ^ cur.length)).any fun m =>
      let p := tab (maskProd cur m)
      !schreierPermEq p 1 && (schreierPermEq p zC || forbid.contains (fixCount p))

@[expose] def derivCheck (forbid : List ℕ) :
    List (Equiv.Perm (Fin 276)) → List (ℕ × List ℤ × ℕ) → Bool
  | cur, [] => badState forbid cur
  | cur, (m, w, i) :: rest =>
    badState forbid cur ||
      (let p := tab (maskProd cur m)
       let c := tab (evalCodes mGens w)
       !schreierPermEq p 1 && schreierPermEq (c * p) (p * c) && decide (i < cur.length) &&
         derivCheck forbid (cur ++ [tab (c * cur.getD i 1 * c⁻¹)]) rest)

@[expose] def parseStep (s : String) : ℕ × List ℤ × ℕ :=
  match s.splitOn ":" with
  | [m, w, i] => ((m.toNat?).getD 0, (w.splitOn ",").filterMap String.toInt?, (i.toNat?).getD 0)
  | _ => (0, [], 0)

@[expose] def parseDeriv (s : String) : List (ℕ × List ℤ × ℕ) :=
  if s.isEmpty then [] else (s.splitOn ";").map parseStep

@[expose] def parseDerivs (s : String) : List (List (ℕ × List ℤ × ℕ)) :=
  (s.splitOn "|").map parseDeriv

@[expose] def daData : String :=
  "1:-6,-2,-4,6,5,6,5,6:1|1:-5,-4,-7,-4,3,4,3,7:1|||||1:-2,-6,-4,-4,5,5,6,2,5,3:1;1:-2,-3,-5,-6,-3,\
  4,7,7,5,7:1||1:-2,-5,-3,-7,-4,2,4,7,5,6:1||||||1:-5,-6,-3,-7,2,7,3,6,5:1|||"

@[expose] def da : List (List (ℕ × List ℤ × ℕ)) := parseDerivs daData

@[expose] def dbData : String :=
  "1:-5,-3,-7,-7,-5,-5,6,4,7,5,5,3,7:1||1:-2,-6,-4,-3,-6,-7,6,4,7,4,7,6,2:1||1:-3,-7,-6,-6,5,7,5,3,\
  2:1|1:-2,-6,-6,-3,4,5,6,6,5,2:1|1:-3,-4,-7,-4,-4,2,5,3,4,6,3:1;1:-4,-6,-3,-7,-7,5,3,7,4,5,5,2:2|\
  1:-2,-7,-5,-4,-7,-6,4,2,7,6,6,7,5,3:1|1:-3,-5,-7,-7,-7,-2,-6,5,3,4,7,7,7,5,3:1;1:-4,-3,-7,-6,-6,\
  -4,7,4,4,2,7,4,2:1|1:-2,-5,-3,-6,-7,-7,4,2,7,7,7,7,3:1;1:-2,-6,-6,-7,-4,-5,6,4,4,3,7,6,6:2||1:-2\
  ,-5,-7,-6,-4,-3,-5,7,5,5,2,7,7,6:1;1:-6,-2,-5,-7,-7,-6,7,5,7,4,5,6,4:1|1:-4,-6,-7,-2,-6,7,5,6,7,\
  6,3,6:1|1:-5,-3,-6,-3,-6,-3,2,5,5,6,6,7,2:1|1:-3,-6,-2,-4,-7,-6,5,4,3,7,5,7:1;1:-2,-6,-4,-3,-7,-\
  7,2,7,6,3,7,5,3:1"

@[expose] def db : List (List (ℕ × List ℤ × ℕ)) := parseDerivs dbData

@[expose] def censusChainCheck : Bool :=
  tQ.check && tQ.orderCertificate == 1024 && saQ.check &&
    saQ.orderCertificate == 512 && sbQ.check && sbQ.orderCertificate == 128 &&
    tGens.all (fun g => schreierPermEq (g * zC) (zC * g)) &&
    saGens.all (fun g => schreierPermEq (g * xa) (xa * g)) &&
    sbGens.all (fun g => schreierPermEq (g * xb) (xb * g))

@[expose] def censusCoverCheck : Bool :=
  repsOK 276 (listTables tGens) (listTables (tGens.map (·⁻¹))) (cosetOrderTables tQ 1 2)
      (tReps.map toTable) 600 &&
    (tReps.map toTable).all (ordTest 276 2) &&
    repsOK 276 (listTables saGens) (listTables (saGens.map (·⁻¹))) (cosetOrderTables saQ 1 2)
      (raReps.map toTable) 600 &&
    (raReps.map toTable).all (ordTest 276 2) &&
    repsOK 276 (listTables sbGens) (listTables (sbGens.map (·⁻¹))) (cosetOrderTables sbQ 1 2)
      (rbReps.map toTable) 600 &&
    (rbReps.map toTable).all (ordTest 276 2)

@[expose] def censusFusionCheck : Bool :=
  fusion.length == tReps.length && fixCount zC == 36 && fixCount xa == 36 &&
    fixCount xb == 12 && !schreierPermEq xa zC && ordTest 276 2 (toTable xa) &&
    ordTest 276 2 (toTable xb) &&
    (tReps.zip fusion).all (fun p =>
      if p.2.1 = 0 then schreierPermEq p.1 zC
      else
        let g := tab (evalCodes mGens p.2.2)
        schreierPermEq (g * p.1 * g⁻¹) (if p.2.1 = 1 then xa else xb)) &&
    (tReps.zip (repSizes 276 (listTables tGens) (listTables (tGens.map (·⁻¹)))
      (tReps.map toTable) 600)).all (fun p =>
      (fixCount p.1 != 12 || decide (8 ≤ p.2)) &&
        (fixCount p.1 != 36 || schreierPermEq p.1 zC || decide (2 ≤ p.2)))

@[expose] def censusArrCheck : Bool :=
  (List.range 7).all (fun k => isInvA 276 co3MArrs[k]! (invCand 276 co3MArrs[k]!) &&
      isInvA 276 (invCand 276 co3MArrs[k]!) co3MArrs[k]!) &&
    (List.range 8).all (fun k => isInvA 276 co3TArrs[k]! (invCand 276 co3TArrs[k]!) &&
      isInvA 276 (invCand 276 co3TArrs[k]!) co3TArrs[k]!) &&
    isInvA 276 co3ZArr (invCand 276 co3ZArr) && isInvA 276 (invCand 276 co3ZArr) co3ZArr

@[expose] def censusDerivCheck : Bool :=
  da.length == raReps.length && db.length == rbReps.length &&
    (raReps.zip da).all (fun p => schreierPermEq p.1 xa || derivCheck [12] [xa, p.1] p.2) &&
    (rbReps.zip db).all (fun p => schreierPermEq p.1 xb || derivCheck [] [xb, p.1] p.2)

end CFSG.ComponentClassification.RankTwoClassical.ExcSp6

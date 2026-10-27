module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

set_option compiler.extract_closed false

@[expose] def listTables {n : ℕ} (gs : List (Equiv.Perm (Fin n))) : Array Table :=
  (gs.map toTable).toArray

@[expose] def invCodes (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

@[expose] def k1Gens : List (Equiv.Perm (Fin 12)) := m12CentWords1.map (evalCodes [m12gA, m12gB])

@[expose] def k1Reps : List (Equiv.Perm (Fin 12)) :=
  [[-2, 4], [-3, -3], [-2, 4, 1], [-3, 4, -2]].map (evalCodes k1Gens)

@[expose] def k3Gens : List (Equiv.Perm (Fin 12)) := m12CentWords2.map (evalCodes [m12gA, m12gB])

@[expose] def k3Reps : List (Equiv.Perm (Fin 12)) := [[-2, -3], [-3, 1]].map (evalCodes k3Gens)

@[expose] def gzWord : List ℤ := [-2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1]

@[expose] def q2Gens : List (Equiv.Perm (Fin 24)) :=
  m12CentWords1.map (evalCodes [m12A1, m12B1]) ++ [m12Sigma]

@[expose] def q2Q : RawSchreierDatum 24 :=
  certificate (by decide) q2Gens [[2, -3, -3], [4, 2, 1], [3, 3, 2, -3], [5, -2, 5, 4, 2]]
    #v[0, 1, 2] (by decide)

@[expose] def q2Reps : List (Equiv.Perm (Fin 24)) :=
  [[-2, 4], [-3, -3], [-2, 5], [-2, 4, 5], [2, 3, 5], [4, 5, -3]].map (evalCodes q2Gens)

@[expose] def q4Gens : List (Equiv.Perm (Fin 24)) :=
  m12CentWords2.map (fun w => evalCodes [m12A1, m12B1] (gzWord ++ w ++ invCodes gzWord)) ++
    [m12Sigma]

@[expose] def q4Q : RawSchreierDatum 24 :=
  certificate (by decide) q4Gens [[3, 1, -2, 1], [-1, 3, 2], [-1, 3, 1, 1, 2]] #v[0, 1, 2]
    (by decide)

@[expose] def q4Reps : List (Equiv.Perm (Fin 24)) :=
  [[2, 3], [1, -3, 4], [1, 3, 4]].map (evalCodes q4Gens)

@[expose] def q5Gens : List (Equiv.Perm (Fin 24)) :=
  m12SigmaCentWords.map (evalCodes [m12A1, m12B1]) ++ [m12Sigma]

@[expose] def q5Q : RawSchreierDatum 24 :=
  certificate (by decide) q5Gens [[3, 1, -3, 1], [-3, 2, 1, 3]] #v[0, 1, 2] (by decide)

@[expose] def permA0 : Equiv.Perm (Fin 12) :=
  List.formPerm [2, 11] * List.formPerm [3, 4] * List.formPerm [7, 10] * List.formPerm [8, 9]

@[expose] def permA1 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [4, 11] * List.formPerm [5, 6] *
    List.formPerm [7, 8] * List.formPerm [9, 10]

@[expose] def g0Word : List ℤ := [-2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2]

@[expose] def g1Word : List ℤ := [1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2]

@[expose] def checkK1 : Bool :=
  repsOK 12 (listTables k1Gens) (listTables (k1Gens.map (·⁻¹))) (cosetOrderTables m12CentQ1 1 4)
      (k1Reps.map toTable) 1000 &&
    (repSizes 12 (listTables k1Gens) (listTables (k1Gens.map (·⁻¹))) (k1Reps.map toTable)
      1000).all (fun k => decide (5 ≤ k)) &&
    (k1Reps.map toTable).all (ordTest 12 4)

@[expose] def checkK3 : Bool :=
  repsOK 12 (listTables k3Gens) (listTables (k3Gens.map (·⁻¹))) (cosetOrderTables m12CentQ2 1 4)
      (k3Reps.map toTable) 1000 &&
    (repSizes 12 (listTables k3Gens) (listTables (k3Gens.map (·⁻¹))) (k3Reps.map toTable)
      1000).all (fun k => decide (5 ≤ k)) &&
    (k3Reps.map toTable).all (ordTest 12 4)

@[expose] def checkQ2 : Bool :=
  q2Q.check && q2Q.orderCertificate == 384 &&
    (q2Gens.all fun g => commT 24 (toTable g) (toTable m12A1)) &&
    repsOK 24 (listTables q2Gens) (listTables (q2Gens.map (·⁻¹))) (cosetOrderTables q2Q 1 4)
      (q2Reps.map toTable) 1000 &&
    (repSizes 24 (listTables q2Gens) (listTables (q2Gens.map (·⁻¹))) (q2Reps.map toTable)
      1000).all (fun k => decide (5 ≤ k)) &&
    (q2Reps.map toTable).all (ordTest 24 4)

@[expose] def checkQ4 : Bool :=
  q4Q.check && q4Q.orderCertificate == 480 &&
    (q4Gens.all fun g => commT 24 (toTable g) (toTable (blockHom (permZ, permZ)))) &&
    repsOK 24 (listTables q4Gens) (listTables (q4Gens.map (·⁻¹))) (cosetOrderTables q4Q 1 4)
      (q4Reps.map toTable) 1000 &&
    (repSizes 24 (listTables q4Gens) (listTables (q4Gens.map (·⁻¹))) (q4Reps.map toTable)
      1000).all (fun k => decide (5 ≤ k)) &&
    (q4Reps.map toTable).all (ordTest 24 4)

@[expose] def checkQ5 : Bool :=
  q5Q.check && q5Q.orderCertificate == 240 &&
    (q5Gens.all fun g => commT 24 (toTable g) (toTable m12Sigma)) &&
    repsOK 24 (listTables q5Gens) (listTables (q5Gens.map (·⁻¹))) (cosetOrderTables q5Q 1 4) []
      1000

end CFSG.ComponentClassification.M12Cover

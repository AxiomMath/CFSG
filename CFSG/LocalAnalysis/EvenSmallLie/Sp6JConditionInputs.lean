module

public import CFSG.Sporadic.Schreier.Co3Sp6
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public meta import CFSG.Sporadic.Schreier.Co3Sp6
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public meta import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public meta import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public meta import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting

public section

namespace CFSG.EvenSmallLie.Sp6

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3
open CFSG.ComponentClassification.M12Cover
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
  (nonempty_mulEquiv_statedSp_of_lieModel)

@[expose] def sp6A : Equiv.Perm (Fin 36) :=
  tab (List.formPerm [0, 8] * List.formPerm [2, 9] * List.formPerm [4, 10] *
    List.formPerm [6, 11] * List.formPerm [12, 16] * List.formPerm [14, 18] *
    List.formPerm [20, 24] * List.formPerm [22, 25] * List.formPerm [28, 32] *
    List.formPerm [30, 35])

@[expose] def sp6B : Equiv.Perm (Fin 36) :=
  tab (List.formPerm [0, 16, 1, 20, 6, 28, 5] * List.formPerm [2, 12, 17, 29, 34, 7, 8] *
    List.formPerm [3, 24, 18, 21, 35, 31, 15] * List.formPerm [4, 32, 19, 13, 23, 30, 26] *
    List.formPerm [10, 22, 11, 25, 14, 33, 27])

@[expose] def sp6Gens : List (Equiv.Perm (Fin 36)) := [sp6A, sp6B]

@[expose] def sp6Q : RawSchreierDatum 36 :=
  certificate (by decide) sp6Gens
    [[-2, -2, 1, 2, 2], [-2, -1, 2, 2, 1], [4, -3, 4, 4, 3, -4, -4, 3, -4],
      [4, -3, -4, -4, 5, -4, -4, 3, -4], [-6, -5, -6, -6, -6, -6, 5, -6, 5],
      [7, -5, -7, -7, 5, 6, -7, 6], [7, -5, 6, -3, -7, 4, 3, -4, 7, 3],
      [-7, -7, -5, 7, 4, -7, 5, -4, 7, 3]]
    #v[0, 1, 2, 4, 8, 12] (by decide)

@[expose] def sp6InvRepWords : List (List ℤ) :=
  [[1], [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2], [1, 2, 1, -2],
    [1, 2, 1, 2, 2, 1, 2, 2, 1, -2, -2, 1, -2, -2, -2]]

@[expose] def sp6InvReps : List (Equiv.Perm (Fin 36)) := sp6InvRepWords.map (evalCodes sp6Gens)

abbrev sp6Rep1 : Equiv.Perm (Fin 36) := sp6InvReps.getD 0 1

abbrev sp6Rep2 : Equiv.Perm (Fin 36) := sp6InvReps.getD 1 1

abbrev sp6Rep3 : Equiv.Perm (Fin 36) := sp6InvReps.getD 2 1

abbrev sp6Rep4 : Equiv.Perm (Fin 36) := sp6InvReps.getD 3 1

@[expose] def sp6CentGens1 : List (Equiv.Perm (Fin 36)) :=
  ([[1], [2, 1, -2], [-2, 1, 2], [2, 2, 1, -2, -2, 1, 2, 2],
    [2, 2, 1, 2, 2, 1, -2, -2, 1, -2, -2]] : List (List ℤ)).map (evalCodes sp6Gens)

@[expose] def sp6CentQ1 : RawSchreierDatum 36 :=
  certificate (by decide) sp6CentGens1
    [[2], [5], [-1, -4, 2, 3], [8, 8, 2, -8, -8], [-5, -8, -5, 9, -8, -8]]
    #v[0, 1, 4, 2, 12] (by decide)

@[expose] def sp6FourReps1 : List (Equiv.Perm (Fin 36)) :=
  ([[4, 4], [1, 4, 4], [2, 3, 5], [2, 4, 4], [2, 3, 2, 4], [2, 3, 2, 4, 4], [2, 3, 2, 4, 5],
    [1, 2, 3, 2, 4, 4], [1, 2, 3, 2, 4, 5], [2, 3, 2, 4, 4, 5]] : List (List ℤ)).map
    (evalCodes sp6CentGens1)

@[expose] def sp6CentGens2 : List (Equiv.Perm (Fin 36)) :=
  ([[1, 2], [2, 1, 2, 2, 1, -2, -2, 1, -2], [1, -2, 1, -2, 1, -2, -2, 1, -2, 1, -2]] :
    List (List ℤ)).map (evalCodes sp6Gens)

@[expose] def sp6CentQ2 : RawSchreierDatum 36 :=
  certificate (by decide) sp6CentGens2
    [[-2, 3], [1, 2, -1], [1, 3, -1], [6, 5, -6], [-2, 5, -1], [-4, -8, -7, 4, 8, 7, 8]]
    #v[0, 1, 4, 2] (by decide)

@[expose] def sp6FourReps2 : List (Equiv.Perm (Fin 36)) :=
  ([[3], [1, -3], [1, 1, 1], [1, 1, 1, 2], [1, 1, 1, 3], [1, 2, 1, 3], [1, 3, 1, 3],
    [1, 1, 1, 1, -3], [1, 1, 1, 2, 3], [1, 1, 2, -1, -3], [1, 2, 3, 1, 3], [1, 2, 3, 1, -3],
    [1, 1, 2, -1, 2, 3], [1, 1, 1, 1, 2, 1, 3]] : List (List ℤ)).map (evalCodes sp6CentGens2)

@[expose] def sp6CentGens3 : List (Equiv.Perm (Fin 36)) :=
  ([[1], [2, 1, -2], [2, 2, 1, -2, -2, 1, 2], [-2, -2, 1, -2, -2, 1, 2, 2, 1, 2, 2],
    [-2, -2, 1, 2, 2, 1, 2, 1, -2, -2, -2, 1, 2, 2],
    [-2, 1, -2, 1, -2, -2, -2, 1, 2, 2, 2, 1, 2, 1, 2]] : List (List ℤ)).map
    (evalCodes sp6Gens)

@[expose] def sp6CentQ3 : RawSchreierDatum 36 :=
  certificate (by decide) sp6CentGens3
    [[2], [3, 6, 3], [-6, -8], [-9, -2, -6, -9, -8, 6, 2], [-2, -8, -4, -8, 1, 5, 3]]
    #v[0, 1, 2, 4] (by decide)

@[expose] def sp6FourReps3 : List (Equiv.Perm (Fin 36)) :=
  ([[1, 5], [3, 3], [3, 4], [3, 5], [4, 5], [1, 3, 3], [1, 3, 4], [1, 3, 5], [1, 4, 5],
    [1, 5, 3], [3, 3, 4], [1, 2, 3, 3], [1, 2, 3, 5], [1, 3, 3, 4], [3, 3, 5, 4],
    [1, 2, 3, 3, 4], [1, 3, 3, 5, 4], [1, 3, 4, 3, 5], [1, 3, 3, 3, 3, 5]] :
    List (List ℤ)).map (evalCodes sp6CentGens3)

@[expose] def sp6CentGens4 : List (Equiv.Perm (Fin 36)) :=
  ([[1], [2, 1, -2], [-2, -2, 1, -2, -2, 1, 2, 2, 1, 2, 2],
    [-2, -2, -2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2],
    [-2, 1, 2, 2, 1, -2, -2, -2, 1, -2, -2, 1, 2, 2, 1, 2, 1, 2],
    [-2, 1, -2, -2, -2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2]] : List (List ℤ)).map
    (evalCodes sp6Gens)

@[expose] def sp6CentQ4 : RawSchreierDatum 36 :=
  certificate (by decide) sp6CentGens4
    [[2], [-3, -4, 2, 6], [-8, -6, 5, 6], [8, -3, -5, 6, 6]] #v[0, 1, 2, 4] (by decide)

@[expose] def sp6FourReps4 : List (Equiv.Perm (Fin 36)) :=
  ([[1, 4], [4, 6], [5, 6], [1, 2, 5], [1, 4, 6], [1, 4, -6], [4, 6, 6], [5, 6, 6],
    [1, 4, 6, 6], [1, 4, -6, -6], [4, 5, 4, 6], [1, 4, 5, 4, 6]] : List (List ℤ)).map
    (evalCodes sp6CentGens4)

@[expose] def centCheck (Q : RawSchreierDatum 36) (c : ℕ) (gs reps : List (Equiv.Perm (Fin 36)))
    (r : Equiv.Perm (Fin 36)) : Bool :=
  Q.check && Q.orderCertificate == c &&
    gs.all (fun g => commT 36 (toTable g) (toTable r)) &&
    repsOK 36 (listTables gs) (listTables (gs.map (·⁻¹))) (cosetOrderTables Q 1 4)
      (reps.map toTable) 4000 &&
    (repSizes 36 (listTables gs) (listTables (gs.map (·⁻¹))) (reps.map toTable) 4000).all
      (fun k => decide (5 ≤ k)) &&
    (reps.map toTable).all (ordTest 36 4)

end CFSG.EvenSmallLie.Sp6

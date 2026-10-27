module

public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38Check
public import Certificates.Data.HuppertU38F.Data

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38

open CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F

@[expose] def liftData1 : LiftData where
  Y := mat8 [0, 0, 1, 1, 0, 0, 0, 1, 0]
  pairs := [
    (0, mat8 [0, 52, 0, 0, 0, 52, 22, 0, 0],
      mat8 [0, 52, 0, 52, 0, 0, 0, 0, 22]),
    (1, mat8 [19, 58, 39, 47, 57, 51, 59, 46, 12],
      mat8 [63, 27, 45, 24, 40, 56, 5, 7, 3]),
    (2, mat8 [7, 45, 24, 5, 27, 56, 3, 63, 40],
      mat8 [55, 47, 29, 47, 19, 59, 29, 59, 37]),
    (0, mat8 [0, 38, 0, 50, 0, 0, 0, 0, 38],
      mat8 [0, 1, 0, 0, 0, 1, 1, 0, 0]),
    (1, mat8 [52, 22, 22, 34, 22, 34, 52, 52, 34],
      mat8 [12, 39, 51, 39, 10, 21, 51, 21, 14]),
    (2, mat8 [12, 29, 28, 51, 55, 58, 39, 47, 25],
      mat8 [51, 28, 37, 55, 21, 46, 58, 19, 39])]
  ws := [
    ([4, 4, 6, 8, 11, 8, 3], dec8 1),
    ([5, 2, 10, 3, 10, 3, 1, 11], dec8 9),
    ([8, 3, 10, 9, 7, 4, 4], dec8 9),
    ([10, 0, 2, 11, 2, 11, 3, 4], dec8 8),
    ([0], dec8 8)]

@[expose] def liftData2 : LiftData where
  Y := mat8 [0, 0, 1, 1, 0, 0, 0, 8, 0]
  pairs := [
    (0, mat8 [0, 50, 0, 38, 0, 0, 0, 0, 38],
      mat8 [52, 22, 22, 34, 22, 34, 52, 52, 34]),
    (1, mat8 [30, 63, 18, 6, 31, 45, 24, 36, 23],
      mat8 [53, 21, 57, 12, 31, 46, 28, 10, 42]),
    (2, mat8 [46, 15, 42, 35, 21, 17, 33, 53, 59],
      mat8 [51, 2, 56, 27, 58, 4, 54, 40, 59]),
    (0, mat8 [1, 8, 8, 1, 1, 9, 8, 1, 8],
      mat8 [8, 9, 8, 8, 1, 1, 1, 1, 8]),
    (1, mat8 [63, 14, 17, 49, 45, 37, 10, 44, 27],
      mat8 [56, 57, 17, 62, 45, 41, 10, 33, 3]),
    (2, mat8 [46, 49, 23, 35, 58, 11, 33, 30, 28],
      mat8 [39, 33, 30, 61, 46, 49, 11, 60, 47])]
  ws := [
    ([9, 3, 8, 2, 4, 6], dec8 1),
    ([0, 11, 6, 4, 2, 6, 10, 4], dec8 1),
    ([6, 5, 8, 3, 9, 2], dec8 8),
    ([5, 11, 6, 3, 5, 6, 10, 1], dec8 8),
    ([1, 6, 0, 6], dec8 1)]

@[expose] def liftData3 : LiftData where
  Y := mat8 [0, 1, 0, 0, 0, 9, 1, 0, 0]
  pairs := [
    (0, mat8 [20, 38, 20, 50, 50, 20, 38, 20, 20],
      mat8 [0, 0, 20, 0, 38, 0, 20, 0, 0]),
    (1, mat8 [58, 26, 31, 53, 59, 44, 49, 61, 51],
      mat8 [23, 45, 2, 36, 31, 7, 3, 54, 30]),
    (2, mat8 [31, 29, 12, 10, 61, 28, 47, 57, 43],
      mat8 [22, 1, 38, 50, 22, 1, 9, 50, 22]),
    (1, mat8 [22, 8, 38, 20, 22, 9, 9, 38, 22],
      mat8 [60, 7, 32, 6, 53, 24, 40, 2, 61]),
    (2, mat8 [53, 7, 18, 48, 31, 40, 24, 32, 42],
      mat8 [12, 18, 53, 35, 10, 48, 36, 42, 14])]
  ws := [
    ([4, 4, 3, 0, 4, 4, 3, 0], dec8 9),
    ([7, 9, 7, 4, 2, 4, 0, 6], dec8 9),
    ([5, 8, 7, 2, 6, 8, 3, 0], dec8 8),
    ([7, 4, 0, 7, 3, 0, 3, 4], dec8 9),
    ([5, 3, 0, 0, 4, 4, 2], dec8 1)]

@[expose] def liftData4 : LiftData where
  Y := mat8 [1, 0, 0, 0, 1, 0, 0, 0, 8]
  pairs := [
    (0, mat8 [34, 22, 22, 52, 52, 22, 22, 34, 22],
      mat8 [8, 9, 1, 1, 1, 1, 9, 8, 1]),
    (1, mat8 [9, 1, 50, 1, 9, 50, 34, 34, 8],
      mat8 [38, 50, 22, 50, 38, 22, 1, 1, 38]),
    (2, mat8 [50, 20, 8, 50, 50, 1, 52, 22, 38],
      mat8 [0, 0, 50, 0, 22, 0, 9, 0, 0]),
    (0, mat8 [34, 22, 22, 22, 34, 22, 52, 52, 22],
      mat8 [8, 9, 8, 9, 8, 8, 9, 9, 1]),
    (1, mat8 [8, 8, 38, 8, 9, 50, 22, 52, 9],
      mat8 [22, 22, 9, 52, 34, 9, 38, 20, 34]),
    (2, mat8 [1, 9, 34, 8, 8, 34, 38, 20, 8],
      mat8 [0, 9, 0, 0, 0, 22, 50, 0, 0])]
  ws := [
    ([3, 9, 4, 4, 8, 3], dec8 1),
    ([2, 4, 8, 6, 9, 1, 4, 0], dec8 1),
    ([8, 3, 4, 4, 8, 2], dec8 1),
    ([1, 4, 10, 7, 4, 8, 1, 8], dec8 1),
    ([10, 1, 10, 0], dec8 8)]

@[expose] def liftData5 : LiftData where
  Y := mat8 [1, 0, 0, 0, 1, 0, 0, 0, 9]
  pairs := [
    (1, mat8 [0, 9, 0, 0, 0, 34, 20, 0, 0],
      mat8 [0, 50, 0, 38, 0, 0, 0, 0, 38]),
    (2, mat8 [9, 8, 20, 8, 8, 50, 22, 34, 9],
      mat8 [22, 22, 1, 34, 52, 1, 38, 50, 34]),
    (0, mat8 [0, 0, 20, 38, 0, 0, 0, 20, 0],
      mat8 [0, 0, 8, 0, 9, 0, 1, 0, 0]),
    (1, mat8 [22, 52, 50, 22, 22, 20, 1, 8, 22],
      mat8 [52, 52, 20, 34, 22, 20, 9, 1, 22]),
    (2, mat8 [34, 52, 9, 22, 52, 1, 20, 20, 22],
      mat8 [34, 52, 9, 22, 22, 9, 20, 38, 34])]
  ws := [
    ([4, 9, 4], dec8 9),
    ([6, 3, 7, 8, 4, 6, 2, 6, 8, 0], dec8 8),
    ([0, 5, 0], dec8 1),
    ([4, 3, 7, 2, 5, 2, 6, 2, 1, 4], dec8 1),
    ([0, 9, 0], dec8 1)]


theorem liftData1_check : liftData1.check = true := by decide +kernel

theorem liftData2_check : liftData2.check = true := by decide +kernel

theorem liftData3_check : liftData3.check = true := by decide +kernel

theorem liftData4_check : liftData4.check = true := by decide +kernel

theorem liftData5_check : liftData5.check = true := by decide +kernel

@[expose] def liftTable : List LiftData := [liftData1, liftData2, liftData3, liftData4, liftData5]

theorem liftTable_cover_bool :
    u38Table.all (fun e => liftTable.any fun D => decide (cm D.Y = cm e.Y)) = true := by
  decide +kernel

theorem exists_liftData {e : U38Entry} (he : e ∈ u38Table) :
    ∃ D : LiftData, D.Y = e.Y ∧ D.check = true := by
  have h := List.all_eq_true.1 liftTable_cover_bool e he
  simp only [List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨D, hD, hY⟩ := h
  refine ⟨D, cm_inj hY, ?_⟩
  simp only [liftTable, List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl
  · exact liftData1_check
  · exact liftData2_check
  · exact liftData3_check
  · exact liftData4_check
  · exact liftData5_check

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38

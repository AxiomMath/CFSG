module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.LinearAlgebra

open Matrix

variable (K : Type*) [CommRing K]

@[expose] def exteriorSquareJ : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if i.val + j.val = 3 then 1 else 0

theorem exteriorSquareJ_apply (i j : Fin 4) :
    exteriorSquareJ K i j = if i.val + j.val = 3 then 1 else 0 := rfl

theorem exteriorSquareJ_eq :
    exteriorSquareJ K = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def exteriorSquareIndex : Fin 4 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (1, 3), (2, 3)]

theorem exteriorSquareIndex_zero : exteriorSquareIndex 0 = (0, 1) := rfl

theorem exteriorSquareIndex_one : exteriorSquareIndex 1 = (0, 2) := rfl

theorem exteriorSquareIndex_two : exteriorSquareIndex 2 = (1, 3) := rfl

theorem exteriorSquareIndex_three : exteriorSquareIndex 3 = (2, 3) := rfl

theorem exteriorSquareIndex_fst_lt_snd (a : Fin 4) :
    (exteriorSquareIndex a).1 < (exteriorSquareIndex a).2 := by
  fin_cases a <;> decide

theorem exteriorSquareIndex_injective : Function.Injective exteriorSquareIndex := by
  decide

variable {K}

@[expose] def exteriorSquareMinor (g : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun a b =>
    g (exteriorSquareIndex a).1 (exteriorSquareIndex b).1 *
        g (exteriorSquareIndex a).2 (exteriorSquareIndex b).2 -
      g (exteriorSquareIndex a).1 (exteriorSquareIndex b).2 *
        g (exteriorSquareIndex a).2 (exteriorSquareIndex b).1

theorem exteriorSquareMinor_apply (g : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4) :
    exteriorSquareMinor g a b =
      g (exteriorSquareIndex a).1 (exteriorSquareIndex b).1 *
          g (exteriorSquareIndex a).2 (exteriorSquareIndex b).2 -
        g (exteriorSquareIndex a).1 (exteriorSquareIndex b).2 *
          g (exteriorSquareIndex a).2 (exteriorSquareIndex b).1 := rfl

theorem exteriorSquareMinor_apply_eq_det (g : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4) :
    exteriorSquareMinor g a b =
      (!![g (exteriorSquareIndex a).1 (exteriorSquareIndex b).1,
          g (exteriorSquareIndex a).1 (exteriorSquareIndex b).2;
        g (exteriorSquareIndex a).2 (exteriorSquareIndex b).1,
          g (exteriorSquareIndex a).2 (exteriorSquareIndex b).2]).det := by
  rw [Matrix.det_fin_two_of, exteriorSquareMinor_apply]

theorem exteriorSquareMinor_one : exteriorSquareMinor (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [exteriorSquareMinor, exteriorSquareIndex, Matrix.one_apply]

end CFSG.LinearAlgebra

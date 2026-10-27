module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open Matrix

variable {K : Type*} [Field K]

@[expose] def l3LowerBlock (g : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  g.submatrix Fin.succ Fin.succ

theorem l3LowerBlock_one : l3LowerBlock (1 : Matrix (Fin 3) (Fin 3) K) = 1 :=
  Matrix.submatrix_one _ (Fin.succ_injective _)

theorem l3LowerBlock_mul_of_col {g h : Matrix (Fin 3) (Fin 3) K}
    (hg : ∀ i : Fin 2, g i.succ 0 = 0) :
    l3LowerBlock (g * h) = l3LowerBlock g * l3LowerBlock h := by
  ext i j
  simp [l3LowerBlock, Matrix.mul_apply, Fin.sum_univ_succ, hg i]

theorem l3LowerBlock_mul_of_row {g h : Matrix (Fin 3) (Fin 3) K}
    (hh : ∀ j : Fin 2, h 0 j.succ = 0) :
    l3LowerBlock (g * h) = l3LowerBlock g * l3LowerBlock h := by
  ext i j
  simp [l3LowerBlock, Matrix.mul_apply, Fin.sum_univ_succ, hh j]

theorem l3_det_eq_of_col {g : Matrix (Fin 3) (Fin 3) K} (hg : ∀ i : Fin 2, g i.succ 0 = 0) :
    g.det = g 0 0 * (l3LowerBlock g).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [l3LowerBlock, hg]

theorem l3_det_eq_of_row {g : Matrix (Fin 3) (Fin 3) K} (hg : ∀ j : Fin 2, g 0 j.succ = 0) :
    g.det = g 0 0 * (l3LowerBlock g).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [l3LowerBlock, hg]

variable (E : Type*) [Group E] (j : E →* GL (Fin 3) K)

@[expose] def L3ParabShape : Prop :=
  (∀ (x : E) (i : Fin 2), ((j x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i.succ 0 = 0) ∨
    ∀ (x : E) (i : Fin 2), ((j x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 i.succ = 0

variable {E j}

@[expose] def l3LeviHom (hs : L3ParabShape E j) : E →* GL (Fin 2) K :=
  MonoidHom.toHomUnits
    { toFun := fun x => l3LowerBlock ((j x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      map_one' := by simp [l3LowerBlock_one]
      map_mul' := fun x y => by
        rw [map_mul, Units.val_mul]
        rcases hs with h | h
        · exact l3LowerBlock_mul_of_col (h x)
        · exact l3LowerBlock_mul_of_row (h y) }

theorem l3LeviHom_apply (hs : L3ParabShape E j) (x : E) :
    ((l3LeviHom hs x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      l3LowerBlock ((j x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

theorem l3_sq_eq_one_of_levi_eq_one [CharP K 2] (hs : L3ParabShape E j)
    (hdet : ∀ x, ((j x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) (x : E)
    (hx : l3LeviHom hs x = 1) : (j x) ^ 2 = 1 := by
  have hb : l3LowerBlock ((j x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← l3LeviHom_apply hs, hx, Units.val_one]
  set M : Matrix (Fin 3) (Fin 3) K := ((j x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have e : ∀ a b : Fin 2, M a.succ b.succ = (1 : Matrix (Fin 2) (Fin 2) K) a b := fun a b => by
    rw [← hb]; rfl
  have h11 : M 1 1 = 1 := by simpa using e 0 0
  have h12 : M 1 2 = 0 := by simpa using e 0 1
  have h21 : M 2 1 = 0 := by simpa using e 1 0
  have h22 : M 2 2 = 1 := by simpa using e 1 1
  have hdet' := hdet x
  rw [← hM] at hdet'
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two, ← hM]
  rcases hs with h | h
  · have h10 : M 1 0 = 0 := h x 0
    have h20 : M 2 0 = 0 := h x 1
    have h00 : M 0 0 = 1 := by
      rw [l3_det_eq_of_col (h x), hb, Matrix.det_one, mul_one] at hdet'
      exact hdet'
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h11, h12, h21, h22, h10, h20,
        CharTwo.add_self_eq_zero]
  · have h01 : M 0 1 = 0 := h x 0
    have h02 : M 0 2 = 0 := h x 1
    have h00 : M 0 0 = 1 := by
      rw [l3_det_eq_of_row (h x), hb, Matrix.det_one, mul_one] at hdet'
      exact hdet'
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h11, h12, h21, h22, h01, h02,
        CharTwo.add_self_eq_zero]

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end

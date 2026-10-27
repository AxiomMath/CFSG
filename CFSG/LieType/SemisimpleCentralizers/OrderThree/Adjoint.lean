module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type*} [Field K]

theorem map_transpose_mul (h : UnitaryFieldData p f K) {ι κ ν : Type*} [Fintype κ]
    (A : Matrix ι κ K) (B : Matrix κ ν K) :
    ((A * B).map h.bar)ᵀ = (B.map h.bar)ᵀ * (A.map h.bar)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem map_transpose_map_transpose (h : UnitaryFieldData p f K) {ι κ : Type*}
    (A : Matrix ι κ K) : (((A.map h.bar)ᵀ).map h.bar)ᵀ = A := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, UnitaryFieldData.bar_bar]

theorem map_transpose_eq_iff (h : UnitaryFieldData p f K) {ι κ : Type*} {M : Matrix ι κ K}
    {M' : Matrix κ ι K} : (M.map h.bar)ᵀ = M' ↔ (M'.map h.bar)ᵀ = M := by
  constructor <;> rintro rfl <;> exact map_transpose_map_transpose h _

theorem map_transpose_mul_eq_one_comm (h : UnitaryFieldData p f K) {ι κ : Type*} [Fintype ι]
    [DecidableEq κ] {A B : Matrix ι κ K} (hAB : (A.map h.bar)ᵀ * B = 1) :
    (B.map h.bar)ᵀ * A = 1 := by
  have hstar := congrArg (fun M : Matrix κ κ K => (M.map h.bar)ᵀ) hAB
  rw [map_transpose_mul h (A.map h.bar)ᵀ B, map_transpose_map_transpose h A,
    Matrix.map_one h.bar (map_zero h.bar) (map_one h.bar), Matrix.transpose_one] at hstar
  exact hstar

theorem gramForm_one_mulVec_left (h : UnitaryFieldData p f K) {d k : ℕ}
    (M : Matrix (Fin d) (Fin k) K) (x : Fin k → K) (y : Fin d → K) :
    gramForm h 1 (M *ᵥ x) y = gramForm h 1 x ((M.map h.bar)ᵀ *ᵥ y) := by
  have hx : (fun a => h.bar ((M *ᵥ x) a)) = M.map h.bar *ᵥ fun a => h.bar (x a) := by
    funext a
    simp [mulVec, dotProduct, map_sum]
  rw [gramForm_apply, gramForm_apply, hx, one_mulVec, one_mulVec]
  rw [dotProduct_comm (M.map h.bar *ᵥ fun a => h.bar (x a)) y, dotProduct_mulVec,
    mulVec_transpose, dotProduct_comm]

end CFSG.LieType.SemisimpleCentralizers.OrderThree

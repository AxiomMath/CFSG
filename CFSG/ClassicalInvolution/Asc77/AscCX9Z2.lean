module

public import CFSG.ClassicalInvolution.Asc77.AscCX9Z1

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2U

open Matrix
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm)

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def descH (c t m n : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, t, 0, 0; -(m / c), -(m * σ t / c), 0, 0; 0, 0, 1, t; 0, 0, -(n / c), -(n * σ t / c)]

@[expose] def descHInv (c t m n : K) : Matrix (Fin 4) (Fin 4) K :=
  !![-(σ t / (t - σ t)), -(t * c / (m * (t - σ t))), 0, 0;
    1 / (t - σ t), c / (m * (t - σ t)), 0, 0;
    0, 0, -(σ t / (t - σ t)), -(t * c / (n * (t - σ t)));
    0, 0, 1 / (t - σ t), c / (n * (t - σ t))]

variable {σ}
variable {c t m n : K} (hc : c ≠ 0) (ht : t - σ t ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
include hc ht hm hn

theorem descH_mul_inv : descH σ c t m n * descHInv σ c t m n = 1 := by
  have ht' : t - σ t ≠ 0 := ht
  ext i j
  fin_cases i <;> fin_cases j <;> simp [descH, descHInv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> ring

theorem descHInv_mul : descHInv σ c t m n * descH σ c t m n = 1 := by
  have ht' : t - σ t ≠ 0 := ht
  ext i j
  fin_cases i <;> fin_cases j <;> simp [descH, descHInv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> ring

theorem descent_form :
    descH σ c t m n * spForm 1 1 * (descH σ c t m n)ᵀ = ((t - σ t) / c) • spForm m n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [descH, spForm, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;>
    field_simp <;> ring

theorem descent_form_inv :
    descHInv σ c t m n * spForm m n * (descHInv σ c t m n)ᵀ = (c / (t - σ t)) • spForm 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [descHInv, spForm, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;>
    field_simp <;> ring

omit ht in
theorem descent_map (hσσ : ∀ a, σ (σ a) = a) (hNm : σ m * m = 1) (hNn : σ n * n = 1)
    (hNc : σ c * c = -1) :
    (descH σ c t m n).map σ = c • (spFormInv m n * descH σ c t m n) := by
  have hσm : σ m = m⁻¹ := eq_inv_of_mul_eq_one_left hNm
  have hσn : σ n = n⁻¹ := eq_inv_of_mul_eq_one_left hNn
  have hσc : σ c = -c⁻¹ := by
    rw [eq_neg_iff_add_eq_zero]
    field_simp
    linear_combination hNc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [descH, spFormInv, map_div₀, hσσ, hσm, hσn, hσc] <;> field_simp

theorem descent_map_inv (hσσ : ∀ a, σ (σ a) = a) (hNm : σ m * m = 1) (hNn : σ n * n = 1)
    (hNc : σ c * c = -1) :
    (descHInv σ c t m n).map σ = c⁻¹ • (descHInv σ c t m n * spForm m n) := by
  have hσm : σ m = m⁻¹ := eq_inv_of_mul_eq_one_left hNm
  have hσn : σ n = n⁻¹ := eq_inv_of_mul_eq_one_left hNn
  have hσc : σ c = -c⁻¹ := by
    rw [eq_neg_iff_add_eq_zero]
    field_simp
    linear_combination hNc
  have hσt : σ t - t ≠ 0 := by
    intro h
    apply ht
    linear_combination -h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [descHInv, spForm, map_div₀, hσσ, hσm, hσn, hσc] <;> field_simp <;> ring

end CFSG.ClassicalInvolution.Asc77.CX.MF2U

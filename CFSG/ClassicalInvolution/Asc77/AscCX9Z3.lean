module

public import CFSG.ClassicalInvolution.Asc77.AscCX9Z2

public noncomputable section

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2U

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm)

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem spForm_transpose (m n : K) : (spForm m n)ᵀ = -spForm m n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spForm]

theorem spFormInv_transpose (m n : K) : (spFormInv m n)ᵀ = -spFormInv m n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spFormInv]

variable {c t m n : K} (hc : c ≠ 0) (ht : t - σ t ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
include hc ht hm hn

theorem form_conj {y : Matrix (Fin 4) (Fin 4) K} (hy : y * spForm 1 1 * yᵀ = spForm 1 1) :
    descH σ c t m n * y * descHInv σ c t m n * spForm m n *
      (descH σ c t m n * y * descHInv σ c t m n)ᵀ = spForm m n := by
  have hf := descent_form_inv hc ht hm hn (σ := σ)
  have hf' := descent_form hc ht hm hn (σ := σ)
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  calc descH σ c t m n * y * descHInv σ c t m n * spForm m n *
        ((descHInv σ c t m n)ᵀ * (yᵀ * (descH σ c t m n)ᵀ))
      = descH σ c t m n * y * (descHInv σ c t m n * spForm m n * (descHInv σ c t m n)ᵀ) *
          yᵀ * (descH σ c t m n)ᵀ := by simp only [Matrix.mul_assoc]
    _ = (c / (t - σ t)) • (descH σ c t m n * (y * spForm 1 1 * yᵀ) * (descH σ c t m n)ᵀ) := by
        rw [hf, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = spForm m n := by
        rw [hy, hf', smul_smul, div_mul_div_comm, mul_comm c, div_self (mul_ne_zero ht hc),
          one_smul]

theorem unitary_conj (hσσ : ∀ a, σ (σ a) = a) (hNm : σ m * m = 1) (hNn : σ n * n = 1)
    (hNc : σ c * c = -1) {y y' : Matrix (Fin 4) (Fin 4) K} (hyσ : y.map σ = y)
    (hy : y * spForm 1 1 * yᵀ = spForm 1 1) (hyy : y' * y = 1) :
    conjTr σ (descH σ c t m n * y * descHInv σ c t m n) *
      (descH σ c t m n * y * descHInv σ c t m n) = 1 := by
  have hHi := descHInv_mul hc ht hm hn (σ := σ)
  have hHi' := descH_mul_inv hc ht hm hn (σ := σ)
  have hform := form_conj hc ht hm hn (σ := σ) hy
  set Y := descH σ c t m n * y * descHInv σ c t m n with hY
  set Y' := descH σ c t m n * y' * descHInv σ c t m n with hY'
  have hYY : Y' * Y = 1 := by
    calc Y' * Y = descH σ c t m n * y' * (descHInv σ c t m n * descH σ c t m n) * y *
          descHInv σ c t m n := by simp only [hY, hY', Matrix.mul_assoc]
      _ = 1 := by rw [hHi, Matrix.mul_one, Matrix.mul_assoc (descH σ c t m n), hyy,
            Matrix.mul_one, hHi']
  have hσY : Y.map σ = spFormInv m n * Y * spForm m n := by
    rw [hY, Matrix.map_mul, Matrix.map_mul, descent_map hc hm hn hσσ hNm hNn hNc,
      descent_map_inv hc ht hm hn hσσ hNm hNn hNc, hyσ]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
      Matrix.mul_assoc]
  have hYt : Yᵀ = spFormInv m n * Y' * spForm m n := by
    calc Yᵀ = spFormInv m n * ((Y' * Y) * spForm m n) * Yᵀ := by
          rw [hYY, Matrix.one_mul, spFormInv_mul hm hn, Matrix.one_mul]
      _ = spFormInv m n * Y' * (Y * spForm m n * Yᵀ) := by simp only [Matrix.mul_assoc]
      _ = spFormInv m n * Y' * spForm m n := by rw [hform]
  rw [conjTr, hσY, Matrix.transpose_mul, Matrix.transpose_mul, spForm_transpose,
    spFormInv_transpose, hYt]
  calc _ = (spForm m n * spFormInv m n) * Y' * (spForm m n * spFormInv m n) * Y := by
        simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    _ = 1 := by rw [spForm_mul_inv hm hn, Matrix.one_mul, Matrix.mul_one, hYY]

theorem descend_fixed (hσσ : ∀ a, σ (σ a) = a) (hNm : σ m * m = 1) (hNn : σ n * n = 1)
    (hNc : σ c * c = -1) {x x' : Matrix (Fin 4) (Fin 4) K} (hxσ : x.map σ = x'ᵀ)
    (hxx : x' * x = 1) (hx : x * spForm m n * xᵀ = spForm m n) :
    (descHInv σ c t m n * x * descH σ c t m n).map σ =
      descHInv σ c t m n * x * descH σ c t m n := by
  have hxG : spForm m n * x'ᵀ = x * spForm m n := by
    calc spForm m n * x'ᵀ = x * spForm m n * xᵀ * x'ᵀ := by rw [hx]
      _ = x * spForm m n * (x' * x)ᵀ := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = x * spForm m n := by rw [hxx, Matrix.transpose_one, Matrix.mul_one]
  rw [Matrix.map_mul, Matrix.map_mul, descent_map_inv hc ht hm hn hσσ hNm hNn hNc, hxσ,
    descent_map hc hm hn hσσ hNm hNn hNc]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  calc descHInv σ c t m n * spForm m n * x'ᵀ * (spFormInv m n * descH σ c t m n)
      = descHInv σ c t m n * (spForm m n * x'ᵀ) * spFormInv m n * descH σ c t m n := by
        simp only [Matrix.mul_assoc]
    _ = descHInv σ c t m n * x * descH σ c t m n := by
        rw [hxG]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (spForm m n), spForm_mul_inv hm hn, Matrix.one_mul]

theorem descend_form {x : Matrix (Fin 4) (Fin 4) K} (hx : x * spForm m n * xᵀ = spForm m n) :
    descHInv σ c t m n * x * descH σ c t m n * spForm 1 1 *
      (descHInv σ c t m n * x * descH σ c t m n)ᵀ = spForm 1 1 := by
  have hf := descent_form hc ht hm hn (σ := σ)
  have hf' := descent_form_inv hc ht hm hn (σ := σ)
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  calc descHInv σ c t m n * x * descH σ c t m n * spForm 1 1 *
        ((descH σ c t m n)ᵀ * (xᵀ * (descHInv σ c t m n)ᵀ))
      = descHInv σ c t m n * x * (descH σ c t m n * spForm 1 1 * (descH σ c t m n)ᵀ) *
          xᵀ * (descHInv σ c t m n)ᵀ := by simp only [Matrix.mul_assoc]
    _ = ((t - σ t) / c) •
          (descHInv σ c t m n * (x * spForm m n * xᵀ) * (descHInv σ c t m n)ᵀ) := by
        rw [hf, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = spForm 1 1 := by
        rw [hx, hf', smul_smul, div_mul_div_comm, mul_comm (t - σ t),
          div_self (mul_ne_zero hc ht), one_smul]

end CFSG.ClassicalInvolution.Asc77.CX.MF2U

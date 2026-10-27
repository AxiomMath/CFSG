module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Ring.RingNF

public section

open scoped Matrix

namespace CFSG.OddStandard.HigherRank.YamadaG23

private lemma vecMul_herm {K : Type} [Field K] (σ : K →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : (A.map σ)ᵀ = A) (w : Fin n → K) :
    Matrix.vecMul (σ ∘ w) A = σ ∘ Matrix.mulVec A w := by
  ext j
  simp only [Function.comp_apply, Matrix.mulVec_apply_eq_sum, Matrix.vecMul_apply_eq_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_mul]
  have hEt : σ (A j t) = A t j := by
    have h := congrFun (congrFun hA t) j
    simpa [Matrix.transpose_apply, Matrix.map_apply] using h
  rw [hEt, mul_comm]

private lemma vecMul_smul_herm {K : Type} [Field K] (σ : K →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : (A.map σ)ᵀ = A) (w : Fin n → K) (c : K) :
    Matrix.vecMul (c • (σ ∘ w)) A = c • (σ ∘ Matrix.mulVec A w) := by
  rw [Matrix.smul_vecMul, vecMul_herm σ A hA w]

private lemma term_herm {K : Type} [Field K] (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : (A.map σ)ᵀ = A) (w : Fin n → K) (c : K)
    (hc : σ c = c) :
    ((Matrix.vecMulVec (Matrix.mulVec A w) (Matrix.vecMul (c • (σ ∘ w)) A)).map σ)ᵀ =
      Matrix.vecMulVec (Matrix.mulVec A w) (Matrix.vecMul (c • (σ ∘ w)) A) := by
  ext r s
  rw [Matrix.transpose_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply,
    vecMul_smul_herm σ A hA w c]
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, map_mul, hc, hσ]
  ring

theorem l2_uni_herm {K : Type} [Field K] (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (b₁ b₂ : Matrix (Fin n) (Fin n) K) (hh₁ : (b₁.map σ)ᵀ = b₁) (hh₂ : (b₂.map σ)ᵀ = b₂)
    (hbb : b₁ * b₂ = b₂ * b₁) (w : Fin n → K) (c : K) (hc : σ c = c) :
    ((∑ j : Fin 4, Matrix.vecMulVec (Matrix.mulVec (![1, b₁, b₂, b₁ * b₂] j) w)
        (Matrix.vecMul (c • (σ ∘ w)) (![1, b₁, b₂, b₁ * b₂] j))).map σ)ᵀ =
      ∑ j : Fin 4, Matrix.vecMulVec (Matrix.mulVec (![1, b₁, b₂, b₁ * b₂] j) w)
        (Matrix.vecMul (c • (σ ∘ w)) (![1, b₁, b₂, b₁ * b₂] j)) := by
  classical
  have hA1 : (((1 : Matrix (Fin n) (Fin n) K).map σ)ᵀ = 1) := by
    rw [Matrix.map_one σ σ.map_zero σ.map_one, Matrix.transpose_one]
  have hA12 : (((b₁ * b₂).map σ)ᵀ = b₁ * b₂) := by
    rw [Matrix.map_mul, Matrix.transpose_mul, hh₁, hh₂, ← hbb]
  have hterm : ∀ j : Fin 4,
      ((Matrix.vecMulVec (Matrix.mulVec (![1, b₁, b₂, b₁ * b₂] j) w)
          (Matrix.vecMul (c • (σ ∘ w)) (![1, b₁, b₂, b₁ * b₂] j))).map σ)ᵀ =
        Matrix.vecMulVec (Matrix.mulVec (![1, b₁, b₂, b₁ * b₂] j) w)
          (Matrix.vecMul (c • (σ ∘ w)) (![1, b₁, b₂, b₁ * b₂] j)) := by
    intro j
    fin_cases j
    · simpa using term_herm σ hσ (1 : Matrix (Fin n) (Fin n) K) hA1 w c hc
    · simpa using term_herm σ hσ b₁ hh₁ w c hc
    · simpa using term_herm σ hσ b₂ hh₂ w c hc
    · simpa using term_herm σ hσ (b₁ * b₂) hA12 w c hc
  ext r s
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrFun (congrFun (hterm j) r) s
  rw [Matrix.transpose_apply, Matrix.map_apply] at h
  exact h

end CFSG.OddStandard.HigherRank.YamadaG23

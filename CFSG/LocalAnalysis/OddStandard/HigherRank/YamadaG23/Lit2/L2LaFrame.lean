module

public import Mathlib.Data.Matrix.Basic

public section

open scoped Matrix

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem l2_la_frame {K : Type} [Field K] (hK : (2 : K) ≠ 0) {n : ℕ}
    (a₁ b₁ a₂ b₂ : Matrix (Fin n) (Fin n) K) (hb₁ : b₁ * b₁ = 1) (hb₂ : b₂ * b₂ = 1)
    (h₁ : a₁ * b₁ = -(b₁ * a₁)) (h₂ : a₂ * b₂ = -(b₂ * a₂)) (h₁₂ : a₁ * a₂ = a₂ * a₁)
    (h₁₂' : a₁ * b₂ = b₂ * a₁) (h₂₁ : b₁ * a₂ = a₂ * b₁) (hbb : b₁ * b₂ = b₂ * b₁)
    {e₁ e₂ : K} (he₁ : e₁ * e₁ = 1) (he₂ : e₂ * e₂ = 1) {w ψ : Fin n → K}
    (hw₁ : Matrix.mulVec a₁ w = e₁ • w) (hw₂ : Matrix.mulVec a₂ w = e₂ • w)
    (hψ₁ : Matrix.vecMul ψ a₁ = e₁ • ψ) (hψ₂ : Matrix.vecMul ψ a₂ = e₂ • ψ)
    (hψw : dotProduct ψ w = 1) :
    ∃ (U : Matrix (Fin n) (Fin 4) K) (Φ : Matrix (Fin 4) (Fin n) K), Φ * U = 1 ∧
      U * Φ * a₁ = a₁ * (U * Φ) ∧ U * Φ * b₁ = b₁ * (U * Φ) ∧
      U * Φ * a₂ = a₂ * (U * Φ) ∧ U * Φ * b₂ = b₂ * (U * Φ) ∧
      U * Φ = ∑ j : Fin 4, Matrix.vecMulVec (Matrix.mulVec (![1, b₁, b₂, b₁ * b₂] j) w)
        (Matrix.vecMul ψ (![1, b₁, b₂, b₁ * b₂] j)) := by
  classical
  have hperp : ∀ (a b : Matrix (Fin n) (Fin n) K) (e : K), a * b = -(b * a) →
      Matrix.mulVec a w = e • w → Matrix.vecMul ψ a = e • ψ → e * e = 1 →
      ψ ⬝ᵥ Matrix.mulVec b w = 0 := by
    intro a b e hab haw hψa he
    have hene : e ≠ 0 := by
      intro h
      rw [h, zero_mul] at he
      exact zero_ne_one he
    have h1 : Matrix.mulVec a (Matrix.mulVec b w) = -(e • Matrix.mulVec b w) := by
      rw [Matrix.mulVec_mulVec, hab, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, haw,
        Matrix.mulVec_smul]
    have hP : ψ ⬝ᵥ Matrix.mulVec a (Matrix.mulVec b w)
        = e * (ψ ⬝ᵥ Matrix.mulVec b w) := by
      rw [Matrix.dotProduct_mulVec, hψa, smul_dotProduct, smul_eq_mul]
    have hQ : ψ ⬝ᵥ Matrix.mulVec a (Matrix.mulVec b w)
        = -(e * (ψ ⬝ᵥ Matrix.mulVec b w)) := by
      rw [h1, dotProduct_neg, dotProduct_smul, smul_eq_mul]
    have h3 : e * (ψ ⬝ᵥ Matrix.mulVec b w) = -(e * (ψ ⬝ᵥ Matrix.mulVec b w)) :=
      calc e * (ψ ⬝ᵥ Matrix.mulVec b w)
          = ψ ⬝ᵥ Matrix.mulVec a (Matrix.mulVec b w) := hP.symm
        _ = -(e * (ψ ⬝ᵥ Matrix.mulVec b w)) := hQ
    have h4 : (2 : K) * (e * (ψ ⬝ᵥ Matrix.mulVec b w)) = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h hK
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hene
      · exact h'

  have hb1w : ψ ⬝ᵥ Matrix.mulVec b₁ w = 0 := hperp a₁ b₁ e₁ h₁ hw₁ hψ₁ he₁
  have hb2w : ψ ⬝ᵥ Matrix.mulVec b₂ w = 0 := hperp a₂ b₂ e₂ h₂ hw₂ hψ₂ he₂
  have hab12 : a₁ * (b₁ * b₂) = -((b₁ * b₂) * a₁) := by
    rw [← Matrix.mul_assoc, h₁, Matrix.neg_mul, Matrix.mul_assoc, h₁₂', ← Matrix.mul_assoc]
  have hb12w : ψ ⬝ᵥ Matrix.mulVec (b₁ * b₂) w = 0 :=
    hperp a₁ (b₁ * b₂) e₁ hab12 hw₁ hψ₁ he₁
  have hab12' : a₂ * (b₁ * b₂) = -((b₁ * b₂) * a₂) := by
    rw [← Matrix.mul_assoc, ← h₂₁, Matrix.mul_assoc, h₂, Matrix.mul_neg, ← Matrix.mul_assoc]

  have hbb' : b₂ * b₁ = b₁ * b₂ := hbb.symm
  have hb1_12 : b₁ * (b₁ * b₂) = b₂ := by
    rw [← Matrix.mul_assoc, hb₁, Matrix.one_mul]
  have hb2_12 : b₂ * (b₁ * b₂) = b₁ := by
    rw [← Matrix.mul_assoc, ← hbb, Matrix.mul_assoc, hb₂, Matrix.mul_one]
  have hb12_1 : (b₁ * b₂) * b₁ = b₂ := by
    rw [Matrix.mul_assoc, ← hbb, ← Matrix.mul_assoc, hb₁, Matrix.one_mul]
  have hb12_2 : (b₁ * b₂) * b₂ = b₁ := by
    rw [Matrix.mul_assoc, hb₂, Matrix.mul_one]
  have hb12_12 : (b₁ * b₂) * (b₁ * b₂) = 1 := by
    rw [Matrix.mul_assoc, hb2_12, hb₁]

  let X : Fin 4 → Matrix (Fin n) (Fin n) K := ![1, b₁, b₂, b₁ * b₂]

  let s : Fin 4 → K := ![1, -1, 1, -1]
  have ha1X : ∀ j, a₁ * X j = s j • (X j * a₁) := by
    intro j
    fin_cases j <;>
      simp [X, s, h₁, h₁₂', hab12, Matrix.one_mul, Matrix.mul_one, neg_smul, one_smul]
  have ha1X' : ∀ j, X j * a₁ = s j • (a₁ * X j) := by
    intro j
    fin_cases j <;>
      simp [X, s, h₁, h₁₂', hab12, Matrix.one_mul, Matrix.mul_one, neg_smul, one_smul,
        neg_neg]

  let t : Fin 4 → K := ![1, 1, -1, -1]
  have ha2X : ∀ j, a₂ * X j = t j • (X j * a₂) := by
    intro j
    fin_cases j <;>
      simp [X, t, h₂, h₂₁, hab12', Matrix.one_mul, Matrix.mul_one, neg_smul, one_smul]
  have ha2X' : ∀ j, X j * a₂ = t j • (a₂ * X j) := by
    intro j
    fin_cases j <;>
      simp [X, t, h₂, h₂₁, hab12', Matrix.one_mul, Matrix.mul_one, neg_smul, one_smul,
        neg_neg]

  let σ : Fin 4 → Fin 4 := ![1, 0, 3, 2]
  have hσ : ∀ j, σ (σ j) = j := by
    intro j
    fin_cases j <;> rfl
  let eσ : Equiv (Fin 4) (Fin 4) :=
    Equiv.ofBijective σ (show Function.Involutive σ from hσ).bijective
  have heσ : ∀ j, eσ j = σ j := fun j => rfl
  have hb1X : ∀ j, b₁ * X j = X (σ j) := by
    intro j
    fin_cases j <;>
      simp [X, σ, hb₁, hbb', hb1_12, Matrix.one_mul, Matrix.mul_one]
  have hb1X' : ∀ j, X j * b₁ = X (σ j) := by
    intro j
    fin_cases j <;>
      simp [X, σ, hb₁, hbb', hb12_1, Matrix.one_mul, Matrix.mul_one]

  let σ' : Fin 4 → Fin 4 := ![2, 3, 0, 1]
  have hσ' : ∀ j, σ' (σ' j) = j := by
    intro j
    fin_cases j <;> rfl
  let eσ' : Equiv (Fin 4) (Fin 4) :=
    Equiv.ofBijective σ' (show Function.Involutive σ' from hσ').bijective
  have heσ' : ∀ j, eσ' j = σ' j := fun j => rfl
  have hb2X : ∀ j, b₂ * X j = X (σ' j) := by
    intro j
    fin_cases j <;>
      simp [X, σ', hb₂, hbb', hb2_12, Matrix.one_mul, Matrix.mul_one]
  have hb2X' : ∀ j, X j * b₂ = X (σ' j) := by
    intro j
    fin_cases j <;>
      simp [X, σ', hb₂, hb12_2, Matrix.one_mul, Matrix.mul_one]

  have hcomm_smul : ∀ (c : Matrix (Fin n) (Fin n) K) (lam : Fin 4 → K),
      (∀ j, c *ᵥ (X j *ᵥ w) = lam j • (X j *ᵥ w)) →
      (∀ j, (ψ ᵥ* X j) ᵥ* c = lam j • (ψ ᵥ* X j)) →
      c * (∑ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j))
        = (∑ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j)) * c := by
    intro c lam hu hv
    rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have h1 : c * Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j)
        = lam j • Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j) := by
      rw [Matrix.mul_vecMulVec, hu j, Matrix.smul_vecMulVec]
    have h2 : Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j) * c
        = lam j • Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j) := by
      rw [Matrix.vecMulVec_mul, hv j, Matrix.vecMulVec_smul]
    rw [h1, h2]

  have hu1 : ∀ j, a₁ *ᵥ (X j *ᵥ w) = (s j * e₁) • (X j *ᵥ w) := by
    intro j
    rw [Matrix.mulVec_mulVec, ha1X j, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hw₁,
      Matrix.mulVec_smul, smul_smul]
  have hv1 : ∀ j, (ψ ᵥ* X j) ᵥ* a₁ = (s j * e₁) • (ψ ᵥ* X j) := by
    intro j
    rw [Matrix.vecMul_vecMul, ha1X' j, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul, hψ₁,
      Matrix.smul_vecMul, smul_smul]
  have hu2 : ∀ j, a₂ *ᵥ (X j *ᵥ w) = (t j * e₂) • (X j *ᵥ w) := by
    intro j
    rw [Matrix.mulVec_mulVec, ha2X j, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hw₂,
      Matrix.mulVec_smul, smul_smul]
  have hv2 : ∀ j, (ψ ᵥ* X j) ᵥ* a₂ = (t j * e₂) • (ψ ᵥ* X j) := by
    intro j
    rw [Matrix.vecMul_vecMul, ha2X' j, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul, hψ₂,
      Matrix.smul_vecMul, smul_smul]

  have hb1_mul : ∀ j, b₁ * Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j)
      = Matrix.vecMulVec (X (σ j) *ᵥ w) (ψ ᵥ* X j) := by
    intro j
    rw [Matrix.mul_vecMulVec, Matrix.mulVec_mulVec, hb1X j]
  have hb1_mul' : ∀ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j) * b₁
      = Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X (σ j)) := by
    intro j
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, hb1X' j]
  have hb1P : b₁ * (∑ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j))
      = (∑ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j)) * b₁ := by
    have hsum : (∑ j, Matrix.vecMulVec (X (σ j) *ᵥ w) (ψ ᵥ* X j))
        = ∑ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X (σ j)) := by
      have h := Equiv.sum_comp eσ (fun k => Matrix.vecMulVec (X k *ᵥ w) (ψ ᵥ* X (σ k)))
      simpa [heσ, hσ] using h
    rw [Matrix.mul_sum, Matrix.sum_mul]
    simp only [hb1_mul, hb1_mul']
    exact hsum

  have hb2_mul : ∀ j, b₂ * Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j)
      = Matrix.vecMulVec (X (σ' j) *ᵥ w) (ψ ᵥ* X j) := by
    intro j
    rw [Matrix.mul_vecMulVec, Matrix.mulVec_mulVec, hb2X j]
  have hb2_mul' : ∀ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j) * b₂
      = Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X (σ' j)) := by
    intro j
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, hb2X' j]
  have hb2P : b₂ * (∑ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j))
      = (∑ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j)) * b₂ := by
    have hsum : (∑ j, Matrix.vecMulVec (X (σ' j) *ᵥ w) (ψ ᵥ* X j))
        = ∑ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X (σ' j)) := by
      have h := Equiv.sum_comp eσ' (fun k => Matrix.vecMulVec (X k *ᵥ w) (ψ ᵥ* X (σ' k)))
      simpa [heσ', hσ'] using h
    rw [Matrix.mul_sum, Matrix.sum_mul]
    simp only [hb2_mul, hb2_mul']
    exact hsum

  let U : Matrix (Fin n) (Fin 4) K := Matrix.of fun r j => (X j *ᵥ w) r
  let Φ : Matrix (Fin 4) (Fin n) K := Matrix.of fun j r => (ψ ᵥ* X j) r
  have hP : U * Φ = ∑ j, Matrix.vecMulVec (X j *ᵥ w) (ψ ᵥ* X j) := by
    ext r s
    rw [Matrix.mul_apply, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hΦU : ∀ j k : Fin 4, (Φ * U) j k = ψ ⬝ᵥ Matrix.mulVec (X j * X k) w := by
    intro j k
    rw [Matrix.mul_apply]
    change (ψ ᵥ* X j) ⬝ᵥ (X k *ᵥ w) = ψ ⬝ᵥ ((X j * X k) *ᵥ w)
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  have hFU : Φ * U = 1 := by
    ext j k
    rw [hΦU j k]
    fin_cases j <;> fin_cases k <;>
      simp [X, hb₁, hb₂, hbb', hb1_12, hb2_12, hb12_1, hb12_2, hb12_12, hψw, hb1w,
        hb2w, hb12w, Matrix.one_mulVec, Matrix.one_mul, Matrix.mul_one]
  refine ⟨U, Φ, hFU, ?_, ?_, ?_, ?_, hP⟩
  · rw [hP]
    exact (hcomm_smul a₁ (fun j => s j * e₁) hu1 hv1).symm
  · rw [hP]
    exact hb1P.symm
  · rw [hP]
    exact (hcomm_smul a₂ (fun j => t j * e₂) hu2 hv2).symm
  · rw [hP]
    exact hb2P.symm

end CFSG.OddStandard.HigherRank.YamadaG23

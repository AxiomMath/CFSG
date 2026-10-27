module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcEig

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Module Matrix

variable {K : Type} [Field K] {d : ℕ}

theorem dot_similitude {R S : Matrix (Fin d) (Fin d) K} {μ : K} (hSR : Sᵀ * R * S = μ • R)
    (v w : Fin d → K) : (S *ᵥ v) ⬝ᵥ R *ᵥ (S *ᵥ w) = μ * (v ⬝ᵥ R *ᵥ w) := by
  have e : ∀ y, (S *ᵥ v) ⬝ᵥ y = v ⬝ᵥ (Sᵀ *ᵥ y) := fun y => by
    rw [dotProduct_mulVec, vecMul_transpose]
  rw [e, mulVec_mulVec, mulVec_mulVec, hSR, smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem false_of_klein_similitude (h2 : (2 : K) ≠ 0) {R : Matrix (Fin d) (Fin d) K}
    (hR : Rᵀ = R) (hRdet : R.det ≠ 0) {u₁ u₂ : Matrix (Fin d) (Fin d) K} (h₁ : u₁ * u₁ = 1)
    (h₂ : u₂ * u₂ = 1) (h12 : u₁ * u₂ = u₂ * u₁) (hR₁ : u₁ᵀ * R * u₁ = R)
    (hR₂ : u₂ᵀ * R * u₂ = R) (hk₁ : finrank K (negE u₁) % 4 = 2)
    (hk₂ : finrank K (negE u₂) % 4 = 2) (hk₃ : finrank K (negE (u₁ * u₂)) % 4 = 2)
    {S : Matrix (Fin d) (Fin d) K} (hS₁ : S * u₁ = u₁ * S) (hS₂ : S * u₂ = u₂ * S) {l μ : K}
    (hl : l ≠ 0) (hS2 : S * S = l • 1) (hSR : Sᵀ * R * S = μ • R)
    (hμ : μ = -l ∨ (μ = l ∧ ¬ IsSquare l)) : False := by
  have hodd := odd_finrank_joint h2 h₁ h₂ h12 hk₁ hk₂ hk₃
  have hnd := nondeg_joint h2 hRdet h₁ h₂ h12 hR₁ hR₂
  have hSW : ∀ w ∈ negE u₁ ⊓ posE u₂, S *ᵥ w ∈ negE u₁ ⊓ posE u₂ := by
    intro w hw
    obtain ⟨hw₁, hw₂⟩ := Submodule.mem_inf.1 hw
    rw [mem_negE] at hw₁
    rw [mem_posE] at hw₂
    refine Submodule.mem_inf.2 ⟨mem_negE.2 ?_, mem_posE.2 ?_⟩
    · rw [mulVec_mulVec, ← hS₁, ← mulVec_mulVec, hw₁, mulVec_neg]
    · rw [mulVec_mulVec, ← hS₂, ← mulVec_mulVec, hw₂]
  have hT2 : ∀ w ∈ negE u₁ ⊓ posE u₂, S *ᵥ (S *ᵥ w) = l • w := fun w _ => by
    rw [mulVec_mulVec, hS2, smul_mulVec, one_mulVec]
  obtain ⟨he, hsq⟩ := similitude_pow_eq hR hnd hSW hT2 fun v _ w _ => dot_similitude hSR v w
  obtain ⟨k, hk⟩ := hodd
  rcases hμ with hμ | ⟨-, hns⟩
  · rw [hμ, Odd.neg_pow ⟨k, hk⟩] at he
    have h0 : (2 : K) * l ^ finrank K ↥(negE u₁ ⊓ posE u₂) = 0 := by linear_combination -he
    exact pow_ne_zero _ hl ((mul_eq_zero.1 h0).resolve_left h2)
  · apply hns
    obtain ⟨r, hr⟩ := hsq
    rw [hk, pow_succ, pow_mul] at hr
    have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl
    refine ⟨r / l ^ k, ?_⟩
    field_simp
    linear_combination hr

theorem even_finrank_of_skew {R A : Matrix (Fin d) (Fin d) K} (hR : Rᵀ = R) (h2 : (2 : K) ≠ 0)
    (hAR : Aᵀ * R = -(R * A)) {a₀ : K} (ha₀ : a₀ ≠ 0) (hA2 : A * A = a₀ • 1)
    {W : Submodule K (Fin d → K)} (hW : ∀ v ∈ W, (∀ u ∈ W, v ⬝ᵥ R *ᵥ u = 0) → v = 0)
    (hAW : ∀ w ∈ W, A *ᵥ w ∈ W) : Even (finrank K W) := by
  have hARA : Aᵀ * R * A = (-a₀) • R := by
    rw [hAR, neg_mul, Matrix.mul_assoc, hA2, Matrix.mul_smul, Matrix.mul_one, neg_smul]
  have hT2 : ∀ w ∈ W, A *ᵥ (A *ᵥ w) = a₀ • w := fun w _ => by
    rw [mulVec_mulVec, hA2, smul_mulVec, one_mulVec]
  obtain ⟨he, -⟩ := similitude_pow_eq hR hW hAW hT2 fun v _ w _ => dot_similitude hARA v w
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [Odd.neg_pow hodd] at he
  have h0 : (2 : K) * a₀ ^ finrank K W = 0 := by linear_combination -he
  exact pow_ne_zero _ ha₀ ((mul_eq_zero.1 h0).resolve_left h2)

end CFSG.ComponentClassification.Burgoyne.DX

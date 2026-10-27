module

public import CFSG.LocalAnalysis.ABGTheoremB.Setting

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

universe u

namespace Setting

variable {G : Type u} [Group G] (σ : Setting G)

@[expose] def NotTotallyInvertedOrdinary : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ¬ σ.TotallyInverted r → σ.Ordinary r

structure CorollaryV61 [Finite G] : Prop where
  sylow_centralized_or_inverted : ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, IsSylowOf r R σ.ON →
    σ.T ≤ Subgroup.normalizer (R : Set G) →
      R ≤ Subgroup.centralizer ({σ.x₂} : Set G) ∨ ∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ = y⁻¹
  layer : ∃ J : Subgroup G, J ≤ σ.L₀ ∧ σ.L₀ = J ⊔ σ.ON ∧
    J ≤ Subgroup.centralizer (σ.ON : Set G) ∧ σ.N ≤ Subgroup.normalizer (J : Set G) ∧
    ((J ⊓ σ.ON = ⊥ ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
        Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (σ.q = 9 ∧ σ.height = 1 ∧ Nat.card (J ⊓ σ.ON : Subgroup G) = 3))
  invertedHall : ∃ B : Subgroup G, B ≤ σ.ON ∧ σ.N ≤ Subgroup.normalizer (B : Set G) ∧
    (∀ y ∈ B, σ.x₂ * y * σ.x₂⁻¹ = y⁻¹) ∧
    ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, IsSylowOf r R σ.ON →
      σ.T ≤ Subgroup.normalizer (R : Set G) → (∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ = y⁻¹) → R ≤ B

end Setting

end CFSG.ABGTheoremB

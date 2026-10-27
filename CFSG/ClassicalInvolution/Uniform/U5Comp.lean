module

public import CFSG.ClassicalInvolution.Q3.LieSystem
public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

@[expose] def CompGen3 (c : Q3.CompData) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ψ : c.G →* X), ψ.ker ≤ Subgroup.center c.G →
    ∀ R₁ ∈ c.fund, ∀ R₂ ∈ c.fund, Nat.card (R₁.map ψ) = 24 → Nat.card (R₂.map ψ) = 24 →
      R₁.map ψ ≠ R₂.map ψ →
      (∃ Q : Subgroup X, Q ≤ R₂.map ψ ∧ Nat.card Q = 8 ∧
        Q ≤ Subgroup.normalizer ((R₁.map ψ : Subgroup X) : Set X)) →
      padicValNat 2 (Nat.card ↥(R₁.map ψ ⊓ R₂.map ψ)) ≤ 1 →
      (∀ z : X, IsUniqueInvolution (R₁.map ψ) z → IsUniqueInvolution (R₂.map ψ) z →
        Commutes (R₁.map ψ) (R₂.map ψ)) →
      ∀ z : X, IsUniqueInvolution (R₁.map ψ) z →
      ∀ A : Subgroup X, IsElemAbelian2 A 2 → A ≤ R₁.map ψ ⊔ R₂.map ψ → z ∈ A →
        ψ.range ≤ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set X) ⊓ ψ.range

end CFSG.ClassicalInvolution.Uniform

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactQCentExp6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), IsOm6Z2 L →
    ∀ Q₁ Q₂ : Subgroup G, Q₁ ≤ L → Q₂ ≤ L →
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) → Nonempty (↥Q₂ ≃* QuaternionGroup 2) →
      ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 → centerIn (Q₁ ⊔ Q₂) = zpowers z →
      z ∉ centerIn L →
      ∀ x ∈ normalizer (L : Set G), x ∈ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) →
        x ^ 4 ∈ centralizer (L : Set G)

@[expose] def Asc82FactQBCent6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), IsOm6Z2 L →
    ∀ Q₁ Q₂ : Subgroup G, Q₁ ≤ L → Q₂ ≤ L →
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) → Nonempty (↥Q₂ ≃* QuaternionGroup 2) →
      ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 → centerIn (Q₁ ⊔ Q₂) = zpowers z →
      (Q₁ ⊔ Q₂) ⊓ centerIn L = ⊥ →
      ∀ B : Subgroup G, B ≤ L ⊓ centralizer ({z} : Set G) → IsElemAb2 B 5 → z ∈ B →
        Nat.card ↥(B ⊓ centerIn L) = 2 →
        ∀ y ∈ normalizer (L : Set G), y ∈ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) →
          y ∈ centralizer (B : Set G) → y * y * z ∉ centralizer (L : Set G)

end CFSG.OddStandard.SmallF3.Omega

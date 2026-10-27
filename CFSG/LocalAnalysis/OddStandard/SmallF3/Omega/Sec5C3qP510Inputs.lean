module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactQCentOrd6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), IsOm6Z2 L → IsI4PlusIn L z →
    ∀ Q₁ Q₂ : Subgroup G, Q₁ ≤ L → Q₂ ≤ L →
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) → Nonempty (↥Q₂ ≃* QuaternionGroup 2) →
      ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 → centerIn (Q₁ ⊔ Q₂) = zpowers z →
      z ∉ centerIn L →
      ∀ Y : Subgroup G, Y ≤ normalizer (L : Set G) →
        Y ≤ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) →
          (centralizer (L : Set G)).relIndex Y ∣ 8 ∧
          ((centralizer (L : Set G)).relIndex Y = 8 →
            ∃ a ∈ Y, ∃ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∉ centralizer (L : Set G))

@[expose] def Asc82FactBCent6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) (r : G) (B : Subgroup G),
    IsOm6Z2 L → twoCoreIn L = zpowers t → B ≤ L ⊓ centralizer ({r} : Set G) → IsElemAb2 B 5 →
      t ∈ B → zpowers t ⊓ layerCent L r = ⊥ → B = zpowers t ⊔ (B ⊓ layerCent L r) →
      (∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α) →
        ∀ c ∈ normalizer (L : Set G), c ∈ centralizer (B : Set G) → c * c ∈ centralizer (L : Set G)

@[expose] def Asc82FactReflCentQ6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), IsOm6Z2 L → IsI4PlusIn L z →
    ∀ Q₁ Q₂ : Subgroup G, Q₁ ≤ L → Q₂ ≤ L →
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) → Nonempty (↥Q₂ ≃* QuaternionGroup 2) →
      ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 → centerIn (Q₁ ⊔ Q₂) = zpowers z →
      z ∉ centerIn L →
      ∀ σ ∈ normalizer (L : Set G), σ * σ = 1 → σ * z = z * σ →
        (∃ α : ℤˣ, InducesTypeSome L σ 6 (-1) 1 α) →
        (∃ α : ℤˣ, InducesTypeSome L (σ * z) 6 (-1) 1 α) →
          σ ∈ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G)

end CFSG.OddStandard.SmallF3.Omega

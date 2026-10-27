module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactSqReflQ6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), IsOm6Z2 L → IsI4PlusIn L z →
    ∀ Q₁ Q₂ : Subgroup G, Q₁ ≤ L → Q₂ ≤ L →
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) → Nonempty (↥Q₂ ≃* QuaternionGroup 2) →
      ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 → centerIn (Q₁ ⊔ Q₂) = zpowers z →
      z ∉ centerIn L →
      ∀ σ ∈ normalizer (L : Set G), σ * σ = 1 → σ * z = z * σ →
        (∃ α : ℤˣ, InducesTypeSome L σ 6 (-1) 1 α) →
        σ ∈ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) →
        ∀ y ∈ normalizer (L : Set G), y * z = z * y → y * y ≠ σ ∧ y * y ≠ σ * z

end CFSG.OddStandard.SmallF3.Omega

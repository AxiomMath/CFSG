module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactPockets6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), IsOm6Z2 L → IsI4PlusIn L z →
    ∃ K₁ K₂ : Subgroup G, Sl23PocketIn L z K₁ ∧ Sl23PocketIn L z K₂ ∧ K₁ ≠ K₂ ∧
      Nonempty (↥(twoCoreIn K₁) ≃* QuaternionGroup 2) ∧
      Nonempty (↥(twoCoreIn K₂) ≃* QuaternionGroup 2) ∧
      ⁅twoCoreIn K₁, twoCoreIn K₂⁆ = ⊥ ∧ Nat.card ↥(twoCoreIn K₁ ⊔ twoCoreIn K₂) = 32 ∧
      centerIn (twoCoreIn K₁ ⊔ twoCoreIn K₂) = zpowers z ∧
      (twoCoreIn K₁ ⊔ twoCoreIn K₂) ⊓ centerIn L = ⊥

@[expose] def Asc82FactQCent6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ Q₁ Q₂ : Subgroup G, Q₁ ≤ L → Q₂ ≤ L →
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) → Nonempty (↥Q₂ ≃* QuaternionGroup 2) →
      ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 → (Q₁ ⊔ Q₂) ⊓ centerIn L = ⊥ →
      ∀ Y : Subgroup G, Odd (Nat.card Y) → Y ≤ normalizer (L : Set G) →
        Y ≤ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) → Y ≤ centralizer (L : Set G)

@[expose] def Asc82FactFrame6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (ρ : Fin 6 → G), IsOm6Z2 L →
    (∀ i, ρ i ∈ normalizer (L : Set G) ∧ ∃ α : ℤˣ, InducesTypeSome L (ρ i) 6 (-1) 1 α) →
    (∀ i j, ρ i * ρ j = ρ j * ρ i) →
    (∀ i j, i ≠ j → ρ i * ρ j ∈ L ⊔ centralizer (L : Set G) ∧
      ρ i * (ρ j)⁻¹ ∉ centralizer (L : Set G)) →
    ∀ x ∈ L ⊔ centralizer (L : Set G), ∀ σ : Equiv.Perm (Fin 6),
      (∀ i, x⁻¹ * ρ i * x * (ρ (σ i))⁻¹ ∈ centralizer (L : Set G)) → Equiv.Perm.sign σ = 1

@[expose] def Asc82FactOutZeta6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ y₁ c : G, y₁ ∈ normalizer (L : Set G) → c ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L y₁ 6 (-1) 1 α) →
      c ∉ L ⊔ centralizer (L : Set G) → c * y₁ ∉ L ⊔ centralizer (L : Set G) →
      (∀ x ∈ oddCoreIn L, y₁ * x = x * y₁ ∧ c * x = x * c) → oddCoreIn L = ⊥

structure Asc82Sec5Facts6 : Prop where
  pockets : Asc82FactPockets6
  qcent : Asc82FactQCent6
  frame : Asc82FactFrame6
  outZeta : Asc82FactOutZeta6

end CFSG.OddStandard.SmallF3.Omega

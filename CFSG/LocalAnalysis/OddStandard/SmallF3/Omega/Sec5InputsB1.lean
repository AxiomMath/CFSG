module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Fact512K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, orderOf t = 2 → centerIn L = zpowers t → ∀ z : G, IsI4PlusIn L z →
      ∃ K₁ K₂ : Subgroup G, Sl23PocketIn L z K₁ ∧ Sl23PocketIn L z K₂ ∧ K₁ ≠ K₂ ∧
        ⁅K₁, K₂⁆ = ⊥ ∧ Nonempty (↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
        Nonempty (↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
        K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G))

structure Asc82Fact512H : Prop where
  inv_class : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, orderOf t = 2 → centerIn L = zpowers t → ∀ z : G, IsI4PlusIn L z →
      ∀ u ∈ twoRes (L ⊓ centralizer ({z} : Set G)), orderOf u = 2 → u ≠ z →
        u ∈ conjClassIn L (t * z)
  meet : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, orderOf t = 2 → centerIn L = zpowers t →
      ∀ r : G, orderOf r = 2 → (∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α) →
        ∀ B : Subgroup G, B ≤ L ⊓ centralizer ({r} : Set G) → IsElemAb2 B 5 → t ∈ B →
          zpowers t ⊓ layerCent L r = ⊥ → B = zpowers t ⊔ (B ⊓ layerCent L r) →
          ∀ z : G, IsI4PlusIn L z → z ∈ zpowers r ⊔ B →
            ∃ p ∈ zpowers r ⊔ B, p ∈ twoRes (L ⊓ centralizer ({z} : Set G)) ∧ p ≠ 1 ∧ p ≠ z

end CFSG.OddStandard.SmallF3.Omega

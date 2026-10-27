module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888F7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5c_card_le_two {G : Type} [Group G] (C : Subgroup G) (z : G)
    (h : ∀ p ∈ C, p = 1 ∨ p = z) : Nat.card ↥C ≤ 2 := by
  have hsub : (C : Set G) ⊆ ({1, z} : Set G) := fun p hp => by
    rcases h p hp with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h1 : Nat.card ↥C ≤ Nat.card ↥({1, z} : Set G) := Nat.card_mono (Set.toFinite _) hsub
  have h2 : Nat.card ↥({1, z} : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  exact h1.trans h2

theorem asc82Fact512H_meet_holds : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    IsOm6Z2 L → ∀ t : G, orderOf t = 2 → centerIn L = zpowers t →
      ∀ r : G, orderOf r = 2 → (∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α) →
        ∀ B : Subgroup G, B ≤ L ⊓ centralizer ({r} : Set G) → IsElemAb2 B 5 → t ∈ B →
          zpowers t ⊓ layerCent L r = ⊥ → B = zpowers t ⊔ (B ⊓ layerCent L r) →
          ∀ z : G, IsI4PlusIn L z → z ∈ zpowers r ⊔ B →
            ∃ p ∈ zpowers r ⊔ B, p ∈ twoRes (L ⊓ centralizer ({z} : Set G)) ∧ p ≠ 1 ∧ p ≠ z := by
  intro G _ _ L hL t ht2 hct r hr2 hind B hB hB32 htB h1 h2 z hz hzA
  have h8 := asc82Fact512M8_holds G L hL t ht2 hct r hr2 hind B hB hB32 htB h1 h2 z hz hzA
  by_contra hcon
  have hle := sec5c_card_le_two ((zpowers r ⊔ B) ⊓ twoRes (L ⊓ centralizer ({z} : Set G))) z
    (fun p hp => by
      by_contra hne
      push_neg at hne
      exact hcon ⟨p, hp.1, hp.2, hne.1, hne.2⟩)
  omega

end CFSG.OddStandard.SmallF3.Omega

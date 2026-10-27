module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82E64Kind3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ E : Subgroup G, E ≤ normalizer (L : Set G) → IsElemAb2 E 6 →
      Nat.card ↥(E ⊓ centralizer (L : Set G)) ≤ 2 →
        Set.ncard {x : G | x ∈ E ∧ ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 3 α} ≤ 20

@[expose] def Asc82Kind2Split : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, t ∈ centerIn L → orderOf t = 2 →
      ∀ s : G, orderOf s = 2 → (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α) →
        ∀ B : Subgroup G, B ≤ L ⊓ centralizer ({s} : Set G) → IsElemAb2 B 5 → t ∈ B →
          zpowers t ⊓ layerCent L s = ⊥ ∧ B = zpowers t ⊔ (B ⊓ layerCent L s)

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactCE16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ X : Subgroup G, X ≤ normalizer (L : Set G) → X ⊓ centralizer (L : Set G) = ⊥ →
      Nat.card X = 16 → (∀ x ∈ X, x * x = 1) →
      (X ≤ L ⊔ centralizer (L : Set G) ∨ ∃ x ∈ X, InducesTypeSome L x 5 1 4 (-1)) ∧
      ∀ F : Finset G, (∀ x ∈ F, x ∈ X ∧ InducesTypeSome L x 5 1 4 (-1)) → F.card ≤ 4

end CFSG.OddStandard.SmallF3.Omega

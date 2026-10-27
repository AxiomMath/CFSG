module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Sec8I3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), IsOm6M L →
    IsSylow2Of S (normalizer (L : Set G)) →
      (∃ (y : G) (α : ℤˣ), InducesTypeSome L y 6 (-1) 1 α ∨ InducesTypeSome L y 6 (-1) 3 α) →
        ∃ B : Subgroup G, B ≤ L ⊓ S ∧ IsElemAb2 B 4 ∧
          ∃ x ∈ S ⊓ centralizer (B : Set G), x ∉ centralizer (L : Set G) ∧
            ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 3 α

end CFSG.OddStandard.SmallF3.Omega

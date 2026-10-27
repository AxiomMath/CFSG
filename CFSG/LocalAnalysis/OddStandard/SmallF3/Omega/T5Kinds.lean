module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def KindM (L : Subgroup G) (s : G) : ℕ → Prop
  | 0 => InducesTypeSome L s 6 (-1) 4 1
  | 1 => InducesTypeSome L s 6 (-1) 4 (-1)
  | 2 => ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α
  | 3 => ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α
  | 4 => InducesProjective L 6 (-1) s
  | _ => InducesOutsideGStar L 6 (-1) s

@[expose] def Asc82Tab6MExcl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ∀ i j : ℕ, i < 6 → j < 6 → i ≠ j → KindM L s i → ¬ KindM L s j

end CFSG.OddStandard.SmallF3.Omega

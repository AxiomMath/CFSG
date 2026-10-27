module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def Asc82Sec5LemmaA : Prop :=
  Asc82Lemma36 → ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G),
    Sec5Ctx G t L S z → ∀ w : G, w ∈ centralizer ({t} : Set G) → w ∈ centralizer ({z} : Set G) →
      Nat.Coprime (orderOf w) 6 → w ∈ centralizer (L : Set G)

end CFSG.OddStandard.SmallF3.Omega

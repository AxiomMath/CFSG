module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

open CFSG CFSG.LocalCores

variable {G : Type*} [Group G]

theorem le_of_isPerfect_of_isSolvable_quotient {L N : Subgroup G} [N.Normal]
    [Group.IsPerfect L] (hN : Group.IsSolvable (G ⧸ N)) : L ≤ N := by
  by_contra hne
  have hmap : L.map (QuotientGroup.mk' N) ≠ ⊥ := by
    intro h
    apply hne
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  have : Nontrivial (L.map (QuotientGroup.mk' N)) := (Subgroup.nontrivial_iff_ne_bot _).2 hmap
  have : Group.IsPerfect (L.map (QuotientGroup.mk' N)) := Group.IsPerfect.map (QuotientGroup.mk' N)
  have := hN
  have : Group.IsSolvable (L.map (QuotientGroup.mk' N)) := inferInstance
  exact Group.IsPerfect.not_isSolvable _ this

variable [Finite G]

end CFSG.ComponentClassification.CatalogueBPrimeJoin

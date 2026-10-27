module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Setting

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup

variable {G : Type} [Group G]

theorem centPair_le_centZ (z t : G) : centPair z t ≤ centZ z := by
  intro g hg
  rw [mem_centralizer_iff] at hg
  exact mem_centralizer_singleton_iff.2 (hg z (mem_sup_left (mem_zpowers z))).symm

end CFSG.EvenSporadicStandard.TwoB

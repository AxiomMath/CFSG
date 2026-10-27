module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.OuterAutomorphisms

theorem congr_mem_inner_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) (α : MulAut G) :
    MulAut.congr e α ∈ inner H ↔ α ∈ inner G := by
  rw [← inner_map_congr e]
  exact Subgroup.mem_map_iff_mem (MulAut.congr e).injective

end CFSG.ComponentClassification.OuterAutomorphisms

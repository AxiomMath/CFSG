module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
public import CFSG.LocalAnalysis.SeitzReduction.EPilotToral

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley

theorem a5LeviRoots_eq_perpRoots : a5LeviRoots = EPilot.perpRoots .E6 :=
  rfl


theorem a5Levi_eq_subgroupOf_perpRoots (K : Type) [Field K] :
    a5Levi K = (rootSpan .E6 K (EPilot.perpRoots .E6)).subgroupOf (adjointGroup .E6 K) :=
  rfl


variable {K : Type} [Field K]

theorem rootSpan_a5LeviRoots_le_centralizer_highRootSL2 :
    rootSpan .E6 K a5LeviRoots ≤
      centralizer (EPilot.highRootSL2 .E6 K : Set (ModGL .E6 K)) :=
  EPilot.rootSpan_perpRoots_le_centralizer_highRootSL2 (Or.inl rfl)


theorem disjoint_highRootSL2_rootSpan_a5LeviRoots [Finite K] [CharP K 2] :
    Disjoint (EPilot.highRootSL2 .E6 K) (rootSpan .E6 K a5LeviRoots) := by
  rw [disjoint_iff_inf_le]
  rintro g ⟨hgJ, hgD⟩
  have hgC : g ∈ adjointGroup .E6 K := rootSpan_le_adjointGroup_E6 _ hgD
  have hz : (⟨⟨g, hgC⟩, mem_a5Levi_iff.2 hgD⟩ : a5Levi K) ∈ center (a5Levi K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : ((y : adjointGroup .E6 K) : ModGL .E6 K) ∈ rootSpan .E6 K a5LeviRoots :=
      mem_a5Levi_iff.1 y.2
    have hc := Subgroup.mem_centralizer_iff.1
      (rootSpan_a5LeviRoots_le_centralizer_highRootSL2 hy) g hgJ
    exact Subtype.ext (Subtype.ext hc.symm)
  rw [center_a5Levi_eq_bot, Subgroup.mem_bot] at hz
  exact congrArg (fun z : a5Levi K => ((z : adjointGroup .E6 K) : ModGL .E6 K)) hz

end CFSG.SeitzReduction.E6Pilot

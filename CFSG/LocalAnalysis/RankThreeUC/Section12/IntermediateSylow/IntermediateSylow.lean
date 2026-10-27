module

public import CFSG.RankThree.PartOne.S12.SectionalRank
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section12

namespace IntermediateSylow

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_sylow {T M : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    CFSG.Open.pCoreOf 2 M ≤ T := by
  obtain ⟨P, rfl⟩ := hT
  have hn : ((CFSG.Open.pCoreOf 2 M).subgroupOf M).Normal := by
    have e : (CFSG.Open.pCoreOf 2 M).subgroupOf M = CFSG.Assembly.pCore 2 M :=
      CFSG.RankThree.PartOne.SectionalRank.pCoreOf_subgroupOf 2 M
    rw [e]
    exact CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_normal_assembly 2 M
  have hp : IsPGroup 2 ((CFSG.Open.pCoreOf 2 M).subgroupOf M) :=
    (CFSG.RankThree.PartOne.SectionalRank.isPGroup_pCoreOf 2 M).comap_subtype
  have := hp.le_sylow_of_normal P
  intro x hx
  have hxM : x ∈ M := Subgroup.map_subtype_le _ hx
  exact ⟨⟨x, hxM⟩, this hx, rfl⟩

end IntermediateSylow

end Section12

end CFSG.LocalAnalysis.RankThreeUC

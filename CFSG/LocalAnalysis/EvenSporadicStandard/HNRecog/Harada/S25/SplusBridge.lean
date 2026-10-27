module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.Splus

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.S25

open Subgroup

theorem SplusFact.facts210 {G : Type} [Group G] {t : G} {z : ↥(centralizer ({t} : Set G))}
    (h : SplusFact z) : Facts210 G t (z : G) := by
  intro Y hY hperf f hf hfk
  refine h.map_injective (centralizer ({t} : Set G)).subtype
    (centralizer ({t} : Set G)).subtype_injective Y ?_ ?_ hperf f hf hfk
  · rw [Subgroup.range_subtype]
    exact hY.trans inf_le_left
  · exact hY.trans inf_le_right

end CFSG.EvenSporadicStandard.HNRecog.Harada.S25

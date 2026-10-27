module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTits

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs

open CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Setup.X6.TitsLat

theorem hasParabolicPair_titsD
    : HasParabolicPair ↥titsD titsFlagStab := by
  obtain ⟨hHt, hNt⟩ := ne_top_of_card card_titsPointStab card_titsLineStab
  refine ⟨titsPointStab, titsLineStab, hHt, hNt,
    generation_of_overgroup_lattice card_titsPointStab card_titsLineStab titsFlagStab_le_point
      card_titsFlagStab tits_overgroups,
    fun α hα => invariant_of_overgroup_lattice card_titsFlagStab card_titsPointStab
      card_titsLineStab titsFlagStab_le_point titsFlagStab_le_line tits_overgroups hα,
    ⟨titsJ.subgroupOf titsD, ?_⟩, ⟨titsK.subgroupOf titsD, ?_⟩⟩
  · refine ParabolicFacts.of_map titsD.subtype titsD.subtype_injective ?_
    rw [← titsH_eq_stab, subgroupOf_map_titsD titsJ_le_titsD]
    exact parabolicFacts_titsH
  · refine ParabolicFacts.of_map titsD.subtype titsD.subtype_injective ?_
    rw [← titsN_eq_stab, subgroupOf_map_titsD titsK_le_titsD]
    exact parabolicFacts_titsN

theorem pairsFor_Tits
    : PairsFor TypeTits := by
  intro G _ _ L R _ hty _ hRN hS
  obtain ⟨e⟩ := titsModelEquiv ↥L 2 1 hty
  exact pairConclusion_of_hasParabolicPair e isSylowTwoOf_flagStab hasParabolicPair_titsD hRN hS

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs

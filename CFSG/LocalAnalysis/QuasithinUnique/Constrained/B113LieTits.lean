module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTits

public section

namespace CFSG.QuasithinUnique.B113Lie.Tits

open CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Setup.X6.TitsLat

theorem parabolicData
    : ParabolicData ↥titsD titsFlagStab {titsPointStab, titsLineStab} := by
  obtain ⟨hHt, hNt⟩ := ne_top_of_card card_titsPointStab card_titsLineStab
  refine ParabolicData.of_pair isSylowTwoOf_flagStab titsFlagStab_le_point
    titsFlagStab_le_line hHt hNt
    (generation_of_overgroup_lattice card_titsPointStab card_titsLineStab titsFlagStab_le_point
      card_titsFlagStab tits_overgroups)
    (fun A hSA hA => ?_) ?_ ?_
    (fun α hα => invariant_of_overgroup_lattice card_titsFlagStab card_titsPointStab
      card_titsLineStab titsFlagStab_le_point titsFlagStab_le_line tits_overgroups hα)
  · rcases tits_overgroups A hSA with h | h | h | h
    · exact Or.inl (h.le.trans titsFlagStab_le_point)
    · exact Or.inl h.le
    · exact Or.inr h.le
    · exact absurd h hA
  · refine (CFSG.QuasithinUnique.Vol2Native.L239.Lie.ParabolicFacts.of_map
      (Q := titsJ.subgroupOf titsD) titsD.subtype titsD.subtype_injective ?_).charTwo
    rw [← titsH_eq_stab, subgroupOf_map_titsD titsJ_le_titsD]
    exact CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.parabolicFacts_titsH
  · refine (CFSG.QuasithinUnique.Vol2Native.L239.Lie.ParabolicFacts.of_map
      (Q := titsK.subgroupOf titsD) titsD.subtype titsD.subtype_injective ?_).charTwo
    rw [← titsN_eq_stab, subgroupOf_map_titsD titsK_le_titsD]
    exact CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.parabolicFacts_titsN

end CFSG.QuasithinUnique.B113Lie.Tits

namespace CFSG.QuasithinUnique.B113Lie

open CFSG.Blueprint CFSG.Sporadic.Schreier.Tits

theorem tits_sylowFacts
    {S : Type} [Group S] [Finite S] (h : ReeTitsModel S .Tits 2 1)
    {T : Subgroup S} (hT : IsSylowTwoOf T ⊤) : SylowFacts S T := by
  obtain ⟨e⟩ := titsModelEquiv S 2 1 h
  have : Finite ↥titsD := inferInstance
  exact SylowFacts.of_mulEquiv_isSylow e Tits.parabolicData.sylowFacts hT

end CFSG.QuasithinUnique.B113Lie

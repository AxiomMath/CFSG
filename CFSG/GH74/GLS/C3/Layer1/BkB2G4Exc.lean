module

public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Induct
public import CFSG.GH74.Filter.Statements
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourIndexTwoLocalB

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.B2G4

open CFSG CFSG.Blueprint CFSG.ComponentClassification CFSG.GH74 CFSG.GH74.Filter Subgroup

theorem exceptionalG4_of_out
    (hout : ∀ s ∈ sporadicOut, S_sporadic s) : ExceptionalG4 := by
  intro G _ _ hg hsimple hnonab hindex hmodel _
  rcases hmodel with hpsl | ⟨⟨e⟩⟩
  · have : IsSimpleGroup (GeneralizedFitting.subgroup G) := hsimple
    have : (GeneralizedFitting.subgroup G).Normal := GeneralizedFitting.normal G
    obtain ⟨-, hbad⟩ := PSL3Four.index_two_local_B (GeneralizedFitting.subgroup G) hpsl hindex
    intro S hne htwo
    rw [hbad S hne htwo, Subgroup.map_bot]
    exact bot_le
  · exact absurd (Gen4.subgroup _ hg) (hout .He (by decide) _ hnonab ⟨e⟩)

end CFSG.GH74.GLS.C3.Layer1.Bk.B2G4

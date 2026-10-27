module

public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches
public import CFSG.LocalAnalysis.OddStandard.ThmCTFacts

public section

namespace CFSG.OddStandard.ThmC

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.ThmC.T

theorem simpleCase_of_gh74 (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput)
    (hSC : SylowComparison) : SimpleCase := by
  intro K _ _ _ hnonab T hTiso
  obtain ⟨e⟩ := hTiso
  exact hSC K (hGH K hnonab (three_le_twoRank tFacts T e) (gen4_of_sylow tFacts T e)) T ⟨e⟩

end CFSG.OddStandard.ThmC

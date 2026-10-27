module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoONLocal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2SporadicMid
public import CFSG.Sporadic.ONOddCore.FixedRankOne

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section ON


theorem onOuterSL2Input_holds : ONOuterSL2Input := by
  intro S _ _ ⟨e⟩ σ hσ hout D hD h2 hDm
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  obtain ⟨hV, -⟩ :=
    Sporadic.ONOddCore.glq_sporadic_outer_involution_fixed_rank_one_ON_exclusion ⟨e⟩ σ hσ2
  exact false_of_fixed_A5_component hD hDm h2
    (fun a ha hσa => on_outer_oddCore_eq_bot e hσ hout ha hσa)
    (fun t ht hσt => on_outer_card_dvd e hσ hout ht hσt) hV

end ON

end CFSG.SeitzReduction.RankOne

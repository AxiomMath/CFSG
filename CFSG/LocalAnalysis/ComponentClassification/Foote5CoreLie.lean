module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCatalogueU
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Blueprint

theorem footeCoreResidualLieInput_of_parts
    (hodd : FooteCoreOddLieInput) (hL34 : FooteCoreL34Input)
    (heven : EvenLieMultiplierOuterInput) : FooteCoreResidualLieInput := by
  intro K _ _ hK a ha Y hY hlie hL2 halt _ hHe
  by_cases hodd' : OddLieType (Y ⧸ Open.fusionZStar Y)
  · exact hodd K hK a ha Y hY hodd' hL2 halt hHe
  have heven' : EvenLieType (Y ⧸ Open.fusionZStar Y) := hlie.resolve_left hodd'
  by_cases hL34' : LieModel (Y ⧸ Open.fusionZStar Y) .PSL 3 2 2
  · exact coreCondition_L34 hL34 footeLBalanceInput_holds ha hY hL34'
  have hbal : UBalanced (Y ⧸ Open.fusionZStar Y) := by
    rintro (h | ⟨n, -, -, ⟨e⟩⟩ | h | h)
    · exact hodd' h
    · exact halt ⟨n, ⟨e⟩⟩
    · exact hL34' h
    · exact hHe h
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  rcases heven _ hna heven' hL34' with hM | hout
  · exact (commutator_mono (commutator_self_le _) le_rfl).trans
      (coreCondition_of_uBalanced_lift catalogAlmostSimpleUnbalancedOutcome_holds hK ha hY hbal hM)
  · exact coreCondition_of_uBalanced_outer catalogAlmostSimpleUnbalancedOutcome_holds hK ha hY
      hbal hout

end CFSG.ComponentClassification.Foote5

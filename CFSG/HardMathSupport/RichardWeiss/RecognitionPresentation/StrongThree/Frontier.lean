module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.SporadicJ1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusAlt
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusSporadic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusLieCharThree

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank


set_option linter.unusedSectionVars false

theorem gls3StronglyThreeEmbeddedPlus_of_open
    (hA6 : ∀ h5 : 5 ≤ 6, Gls3PlusCase (.alternating 6 h5))
    (hM11 : Gls3PlusCase (.sporadic .M11))
    (hR1 : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 →
      CFSG.AGLEmbedding.IsRankOneLieIndex d.1 → Gls3PlusCase (.lie d))
    (hOff : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ 3 → Gls3PlusCase (.lie d)) :
    Gls3StronglyThreeEmbeddedPlus := by
  refine gls3StronglyThreeEmbeddedPlus_of_families (fun n h5 => ?_) (fun d => ?_) (fun s => ?_)
  · rcases (show n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | h7
    · exact gls3PlusCase_alternating_five h5
    · exact hA6 h5
    · exact gls3PlusCase_alternating_of_seven_le n h5 h7
  · by_cases h3 : d.1.characteristic = 3
    · by_cases hr : CFSG.AGLEmbedding.IsRankOneLieIndex d.1
      · exact hR1 d h3 hr
      · exact gls3PlusCase_lie_of_char_three d h3 hr
    · exact hOff d h3
  · by_cases h11 : s = .M11
    · subst h11
      exact hM11
    by_cases hJ1 : s = .J1
    · subst hJ1
      exact gls3PlusCase_J1
    exact gls3PlusCase_sporadic_of_ne s h11 hJ1

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

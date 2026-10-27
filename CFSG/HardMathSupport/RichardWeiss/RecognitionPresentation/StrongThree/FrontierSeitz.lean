module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Frontier
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.FamilySix
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.SporadicM11
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusLieOffChar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusL28
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusL34

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank


set_option linter.unusedSectionVars false

theorem gls3StronglyThreeEmbeddedPlus_of_seitz (hOff : CFSG.AGLEmbedding.OffCharGen)
    (hOut : CFSG.LieType.SeitzGeneration.SeitzOuterLowN)
    (hR1 : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 →
      CFSG.AGLEmbedding.IsRankOneLieIndex d.1 → Gls3PlusCase (.lie d)) :
    Gls3StronglyThreeEmbeddedPlus := by
  refine gls3StronglyThreeEmbeddedPlus_of_open (fun h5 => gls3PlusCase_alternating_six h5)
    gls3PlusCase_M11 hR1 (fun d h3 => ?_)
  by_cases hL28 : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q
  · obtain ⟨q, hq2, hq3, hd⟩ := hL28
    exact gls3PlusCase_lie_L28 d q hq2 hq3 hd
  by_cases hL34 : CFSG.AGLEmbedding.IsLinThreeFourIndex d
  · obtain ⟨q, hq2, hq3, hd⟩ := hL34
    exact gls3PlusCase_lie_L34 d q hq2 hq3 hd
  exact gls3PlusCase_lie_of_offChar_ne hOff hOut d h3 hL28 hL34

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

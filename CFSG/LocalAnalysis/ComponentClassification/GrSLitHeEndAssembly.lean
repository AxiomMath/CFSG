module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGS36
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZInvol

public section

namespace CFSG.ComponentClassification.GrSLit

theorem heldEndStep_of_models
    (hKN : HeldKNormalStep) (hEnd : HeldZStarEndStep) (hB : HeldTwoBTwelveModel)
    (hFour : HeldTwoAFourModel) (hPair : HeldTwoAPairModel) (hGen : HeldTwoAGenerationModel) :
    HeldEndStep :=
  heldEndStep_of_steps hKN hEnd (heldTwoBCentralizerFact_of_model hB) heldTwoALayerFact
    (heldTwoAFourFact_of_model hFour) heldTwoAClassFact (heldTwoAPairFact_of_model hPair)
    (heldTwoAGenerationFact_of_model hGen)

theorem heldEndStep_of_frontiers
    (hKN : HeldKNormalStep) : HeldEndStep :=
  heldEndStep_of_models hKN (heldZStarEndStep_of_facts heldOuterSolvableFact heldInvolAutFact
      heldTwoAKFact heldTwoBFact heldSylowFourFact heldTwoALayerFact
      (heldTwoAFourFact_of_model HeGS.heldTwoAFourModel)
      (heldTwoBCentralizerFact_of_model HeGS.heldTwoBTwelveModel)
      (heldTwoAPairFact_of_model HeGS.heldTwoAPairModel)
      (heldTwoAGenerationFact_of_model HeGS.heldTwoAGenerationModel)) HeGS.heldTwoBTwelveModel HeGS.heldTwoAFourModel
    HeGS.heldTwoAPairModel HeGS.heldTwoAGenerationModel

end CFSG.ComponentClassification.GrSLit

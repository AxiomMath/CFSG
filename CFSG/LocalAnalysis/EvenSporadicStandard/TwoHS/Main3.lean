module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HNFactsProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Sect6

public section

namespace CFSG.EvenSporadicStandard.TwoHS

theorem twoHSGivesHN_of_inputs''
    (hR : HaradaHNRecognitionKP) (hSol : SolomonTwoHSNotFour)
    (hHar : HaradaCentralizerShape) : TwoHSGivesHN :=
  twoHSGivesHN_of_inputs hR (solomonTwoHSCentralizer_of_notFour hSol) hHar hnCentralizerFacts

theorem twoHSGivesHN_of_fusion
    (hR : HaradaHNRecognitionKP) (hS6 : SolomonSection6Fusion)
    (hHar : HaradaCentralizerShape) : TwoHSGivesHN :=
  twoHSGivesHN_of_inputs'' hR hS6.notFour hHar

end CFSG.EvenSporadicStandard.TwoHS

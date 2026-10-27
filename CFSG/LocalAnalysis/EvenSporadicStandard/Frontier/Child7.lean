module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Main3
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGFinal

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic

theorem child7_of_frontier
    (hHaradaHN : TwoHS.HaradaHNRecognitionKP)
    (hGH312 : TwoHS.GH312Fixed) :
    TwoHSGivesHN :=
  TwoHS.twoHSGivesHN_of_fusion hHaradaHN
    (TwoHS.solomonSection6Fusion_of_localAnalysis
      (TwoHS.sect6LocalAnalysis_of_sect7
        (TwoHS.sect7Existence_of_inputs (TwoHS.sect8InputA_of_hHN TwoHS.hnCentralizerFacts)
          (TwoHS.sect8InputU_holdsW hGH312 TwoHS.signDataPGSpXS_proved)
          (TwoHS.sect8InputFy_holdsW hGH312 TwoHS.signDataPGSpXS_proved))))
    TwoHS.haradaCentralizerShape

end CFSG.EvenSporadicStandard.Frontier

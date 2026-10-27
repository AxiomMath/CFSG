module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGFinal

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open CFSG.EvenSporadicStandard

theorem solomonTwoHSCentralizer_of_gh312
    (hGH312 : TwoHS.GH312Fixed) : TwoHS.SolomonTwoHSCentralizer :=
  TwoHS.solomonTwoHSCentralizer_of_notFour
    (TwoHS.SolomonSection6Fusion.notFour
      (TwoHS.solomonSection6Fusion_of_localAnalysis
        (TwoHS.sect6LocalAnalysis_of_sect7
          (TwoHS.sect7Existence_of_inputs (TwoHS.sect8InputA_of_hHN TwoHS.hnCentralizerFacts)
            (TwoHS.sect8InputU_holdsW hGH312 TwoHS.signDataPGSpXS_proved)
            (TwoHS.sect8InputFy_holdsW hGH312 TwoHS.signDataPGSpXS_proved)))))

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

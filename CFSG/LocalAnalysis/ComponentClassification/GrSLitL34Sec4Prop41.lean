module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma47

public section

namespace CFSG.ComponentClassification.GrSLit

theorem l34Prop41_of_inputs
    (hSol : SolomonCommutingCoreInput) (hKG : L34UnbalancedKGroupInput)
    (hU : L34UnbalancingUnitaryStep) (hC : L34UnitaryCentralizerFact)
    (hBor : L34BorelGenerationFact) (hParab : L34ParabolicFact) (hTwo : L34TwoEightsFact)
    (hPar : L34ParabolicGenerationFact) (hExp : L34CenterExponentFact)
    (hEl : L34ElementaryCenterFact) (hCF : L34CentralFourFact) (hSq : L34NoSquareRootFact)
    (hEnd43 : L34Lemma43EndStep) (hWS : L34Lemma46WStep) (hEnd46 : L34Lemma46EndStep)
    (hConn : L34Lemma47ConnectStep) (hSyl : L34EndSylowStep) (hGH : GorensteinHarrisInput)
    (hON : ONanSylowInput) : L34Prop41 :=
  have h43 := l34Lemma43_of_inputs hSol hKG hTwo hPar hExp hEl hEnd43
  have h44 := l34Lemma44_of_inputs hU hC hBor hParab
  have h46 := l34Lemma46_of_inputs hSol hKG h43 h44 hU hC hCF hWS hEnd46
  prop41_of_steps h46 (l34Lemma47_of_inputs h43 h46 hConn hSq)
    (l34Prop41End_of_inputs hSyl hGH hON)

end CFSG.ComponentClassification.GrSLit

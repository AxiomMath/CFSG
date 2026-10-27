module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHS9X
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHWrX
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyInvE
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyThrE
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HNFactsProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyO
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUModelZ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxGH
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxLy
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxU

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

section HNHolds


theorem sect8InputLy_holdsW (hGH : GH312Fixed) (hPG : SignDataPGSpXS) : Sect8InputLy :=
  sect8InputLy_of_signTheoremXW
    (signTheoremXW (gh312WrFixed_of_gh312Fixed hGH) signDataS9X signDataWrX hPG)
    (fun _ _ _ _ _ _ _ _ _ hH =>
      fyModelFacts_of_model hnCentralizerFacts hsThreeClass hsInvolutionClasses hsOuterThree hH)

theorem sect8InputFy_holdsW (hGH : GH312Fixed) (hPG : SignDataPGSpXS) : Sect8InputFy :=
  sect8InputFy_of_ly (sect8InputLy_holdsW hGH hPG)

end HNHolds

section Final


theorem sect8InputU_holdsW (hGH : GH312Fixed) (hPG : SignDataPGSpXS) :
    ∀ hQ : Q0Facts, Sect8InputU hQ := by
  have hS : SignTheoremXW :=
    signTheoremXW (gh312WrFixed_of_gh312Fixed hGH) signDataS9X signDataWrX hPG
  have hF : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G)
      (n : G), Sect7Hyps G L f s y S₀ n → FyModelFacts L f y :=
    fun _ _ _ _ _ _ _ _ _ hH =>
      fyModelFacts_of_model hnCentralizerFacts hsThreeClass hsInvolutionClasses hsOuterThree hH
  have hZ : ModelZ := modelZ_holds hnCentralizerFacts
  exact sect8InputU_of_inputs (sect8InputFy_holdsW hGH hPG) (sect8InputK_of_modelZW hS hF hZ)
    fun hQ => sect8InputO_of_ly hQ (sect8InputLy_holdsW hGH hPG) (knotInLf_holds hQ)
      (cl16OfClass_of_modelZW hS hF hZ hQ)

end Final

end CFSG.EvenSporadicStandard.TwoHS

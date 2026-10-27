module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcInner
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTw
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcD4

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem oddLieCoreFamilyInput_exceptional
    (hF4 : InnerDiagThreeCoreInput .F4) (hE6 : InnerDiagThreeCoreInput .E6)
    (hE8 : InnerDiagThreeCoreInput .E8) (hG2i : G2ThreeInnerCoreInput)
    (hG2o : G2ThreeOuterCoreInput) (hE6g : E6GraphCoreInput) (hE7 : InnerDiagCoreInput .E7)
    (hTE6i : TwistedE6InnerCoreInput) (hTE6g : TwistedE6GraphCoreInput)
    (hD4 : TrialityInnerCoreInput) (hRee : SmallReeInnerCoreInput) :
    ∀ τ : StatedLieTag, τ ∉ classicalTags → OddLieCoreFamilyInput τ := by
  intro τ hτ
  cases τ with
  | PSL => exact absurd (by decide) hτ
  | PSU => exact absurd (by decide) hτ
  | PSp => exact absurd (by decide) hτ
  | POmegaOdd => exact absurd (by decide) hτ
  | POmegaPlus => exact absurd (by decide) hτ
  | POmegaMinus => exact absurd (by decide) hτ
  | G2 => exact oddLieCoreFamilyInput_G2_of_three hG2i hG2o
  | F4 => exact oddLieCoreFamilyInput_F4_of_three hF4
  | E6 => exact oddLieCoreFamilyInput_E6_of_three hE6 hE6g
  | E7 => exact oddLieCoreFamilyInput_E7 hE7
  | E8 => exact oddLieCoreFamilyInput_E8_of_three hE8
  | twistedE6 => exact oddLieCoreFamilyInput_twistedE6 hTE6i hTE6g
  | trialityD4 => exact oddLieCoreFamilyInput_trialityD4 hD4
  | twistedB2 => exact oddLieCoreFamilyInput_twistedB2
  | twistedG2 => exact oddLieCoreFamilyInput_twistedG2 hRee
  | twistedF4 => exact oddLieCoreFamilyInput_twistedF4
  | Tits => exact oddLieCoreFamilyInput_Tits

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc

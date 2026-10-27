module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamClassical
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamExceptional
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamRest
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.SuzRee
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Tits

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator

set_option linter.unusedSectionVars false

section Three

theorem localTwoCrossFamCat_three_all
    (hU2 : PSUTwoThreeBalance) (hSp : SpTwoThreeBalance) (hOrth : OrthTwoThreeInnerBalance)
    (hD4 : D4TrialityPlaneThreeBalance) (hE6H : E6HeisenbergDiagThreeBalance)
    (hTwE6H : TwistedE6HeisenbergDiagThreeBalance) (hTriIn : TriD4InnerThreeBalance)
    (hTriOut : TriD4OuterThreeBalance) (hS6 : ReeF4InnerThreeBalance) :
    ∀ k : LieFamily, LocalTwoCrossFamCat 3 k := fun k =>
  match k with
  | .A => localTwoCrossFamCat_three_A
  | .twistedA => localTwoCrossFamCat_three_twistedA hU2
  | .B => localTwoCrossFamCat_three_B hSp
  | .C => localTwoCrossFamCat_three_C
  | .D => localTwoCrossFamCat_three_D hOrth hD4
  | .twistedD => localTwoCrossFamCat_three_twistedD hOrth
  | .E6 => localTwoCrossFamCat_three_E6 hE6H
  | .E7 => localTwoCrossFamCat_three_E7
  | .E8 => localTwoCrossFamCat_three_E8
  | .F4 => localTwoCrossFamCat_three_F4
  | .G2 => localTwoCrossFamCat_three_G2
  | .twistedE6 => localTwoCrossFamCat_three_twistedE6 hTwE6H
  | .trialityD4 => localTwoCrossFamCat_three_trialityD4 hTriIn hTriOut
  | .suzuki => localTwoCrossFamCat_three_suzuki
  | .reeG2 => localTwoCrossFamCat_three_reeG2
  | .reeF4 => localTwoCrossFamCat_three_reeF4 hS6
  | .tits => localTwoCrossFamCat_three_tits

end Three

section Five

theorem localTwoCrossFamCat_five_all
    (hS7 : ReeF4InnerFiveBalance) (hE7₁ : E7InnerFiveOne) (hE7₂ : E7InnerFiveTwo)
    (hE7₄ : E7InnerFiveFour) (hE6₁ : E6InnerFiveOne) (hE6₄ : E6InnerFiveFour)
    (hTwE6₂ : TwistedE6InnerFiveTwo) (hTwE6₄ : TwistedE6InnerFiveFour) (hF4₄ : F4InnerFiveFour)
    (hE8₄ : E8InnerFiveFour) :
    ∀ k : LieFamily, LocalTwoCrossFamCat 5 k := fun k =>
  match k with
  | .A => localTwoCrossFamCat_five_A
  | .twistedA => localTwoCrossFamCat_five_twistedA
  | .B => localTwoCrossFamCat_five_B
  | .C => localTwoCrossFamCat_five_C
  | .D => localTwoCrossFamCat_five_D
  | .twistedD => localTwoCrossFamCat_five_twistedD
  | .E6 => localTwoCrossFamCat_five_E6 hE6₁ hE6₄
  | .E7 => localTwoCrossFamCat_five_E7 hE7₁ hE7₂ hE7₄
  | .E8 => localTwoCrossFamCat_five_E8 hE8₄
  | .F4 => localTwoCrossFamCat_five_F4 hF4₄
  | .G2 => localTwoCrossFamCat_five_G2
  | .twistedE6 => localTwoCrossFamCat_five_twistedE6 hTwE6₂ hTwE6₄
  | .trialityD4 => localTwoCrossFamCat_five_trialityD4
  | .suzuki => localTwoCrossFamCat_five_suzuki
  | .reeG2 => localTwoCrossFamCat_five_reeG2
  | .reeF4 => localTwoCrossFamCat_five_reeF4 hS7
  | .tits => localTwoCrossFamCat_five_tits

end Five

section Both

theorem localTwoBalanceCrossChar_three_five_of_rows
    (hU2 : PSUTwoThreeBalance) (hSp : SpTwoThreeBalance) (hOrth : OrthTwoThreeInnerBalance)
    (hD4 : D4TrialityPlaneThreeBalance) (hE6H : E6HeisenbergDiagThreeBalance)
    (hTwE6H : TwistedE6HeisenbergDiagThreeBalance) (hTriIn : TriD4InnerThreeBalance)
    (hTriOut : TriD4OuterThreeBalance) (hS6 : ReeF4InnerThreeBalance)
    (hS7 : ReeF4InnerFiveBalance) (hE7₁ : E7InnerFiveOne) (hE7₂ : E7InnerFiveTwo)
    (hE7₄ : E7InnerFiveFour) (hE6₁ : E6InnerFiveOne) (hE6₄ : E6InnerFiveFour)
    (hTwE6₂ : TwistedE6InnerFiveTwo) (hTwE6₄ : TwistedE6InnerFiveFour) (hF4₄ : F4InnerFiveFour)
    (hE8₄ : E8InnerFiveFour) :
    LocalTwoBalanceCrossCharThree ∧ LocalTwoBalanceCrossCharFive :=
  localTwoBalanceCrossChar_three_five_of_cat
    (localTwoCrossFamCat_three_all hU2 hSp hOrth hD4 hE6H hTwE6H hTriIn hTriOut hS6)
    (localTwoCrossFamCat_five_all hS7 hE7₁ hE7₂ hE7₄ hE6₁ hE6₄ hTwE6₂ hTwE6₄ hF4₄ hE8₄)

end Both

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

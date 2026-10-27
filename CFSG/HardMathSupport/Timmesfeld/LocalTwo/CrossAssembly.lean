module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinAll
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisFinal
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthFamilies
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniHeis
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuz
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeG2
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossTits

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.HardMathSupport.Timmesfeld.DefChar


theorem crossCharTwoFamCat_of_not_exceptional
    (hF4 : ReeF4InnerPlaneBalance) (k : LieFamily) (hk : ¬ IsExceptionalFam k) :
    CrossCharTwoFamCat k := by
  cases k with
  | A => exact crossCharTwoFamCat_A linHeisenbergBalance_holds
  | twistedA => exact crossCharTwoFamCat_twistedA
  | B => exact crossCharTwoFamCat_B
  | C => exact crossCharTwoFamCat_C
  | D => exact crossCharTwoFamCat_D
  | twistedD => exact crossCharTwoFamCat_twistedD
  | suzuki => exact crossCharTwoFamCat_suzuki
  | reeG2 => exact crossCharTwoFamCat_reeG2
  | reeF4 => exact crossCharTwoFamCat_reeF4_of_inner hF4
  | tits => exact crossCharTwoFamCat_tits
  | E6 => exact absurd trivial hk
  | E7 => exact absurd trivial hk
  | E8 => exact absurd trivial hk
  | F4 => exact absurd trivial hk
  | G2 => exact absurd trivial hk
  | twistedE6 => exact absurd trivial hk
  | trialityD4 => exact absurd trivial hk

theorem localTwoBalanceCrossCharGtFive_of_exceptional
    (hF4 : ReeF4InnerPlaneBalance)
    (hex : ∀ k, IsExceptionalFam k → CrossCharTwoFamCat k) :
    LocalTwoBalanceCrossCharGtFive :=
  localTwoBalanceCrossCharGtFive_of_classical_and_exceptional
    (crossCharTwoFamCat_of_not_exceptional hF4) hex

end CFSG.HardMathSupport.Timmesfeld.LocalTwo

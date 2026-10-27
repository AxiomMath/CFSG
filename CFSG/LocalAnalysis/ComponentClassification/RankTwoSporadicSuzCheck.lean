module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEnd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzCover
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzMult6
public import Certificates.Certificate15030
public import Certificates.Certificate15031
public import Certificates.Certificate15032
public import Certificates.Certificate15033
public import Certificates.Certificate15034
public import Certificates.Certificate15035
public import Certificates.Certificate15036
public import Certificates.Certificate15037
public import Certificates.Certificate15038

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open CFSG.Sporadic.Recognition.SuzMultiplier

theorem suz_tabCheck :
    CFSG.Sporadic.Recognition.SuzMultiplier.suzTabCheck = true :=
  Certificates.certificate15030

theorem suz_rho0Check :
    CFSG.Sporadic.Recognition.SuzMultiplier.suzRho0Check = true :=
  Certificates.certificate15031

theorem suz_rhoJ2Check :
    CFSG.Sporadic.Recognition.SuzMultiplier.suzRhoJ2Check = true :=
  Certificates.certificate15032

theorem suz_l0Check :
    CFSG.Sporadic.Recognition.SuzMultiplier.SuzIndexP1 :=
  Certificates.certificate15033

theorem suz_l1Check :
    CFSG.Sporadic.Recognition.SuzMultiplier.SuzIndexP2 :=
  Certificates.certificate15034

theorem suz_l2Check :
    CFSG.Sporadic.Recognition.SuzMultiplier.SuzCardP2 :=
  Certificates.certificate15035

theorem suz_checkII :
    ∃ d : CFSG.KC.Census.ConjDataP, suzCheckWII d = true :=
  Certificates.certificate15036

theorem suz_checkExc :
    ∃ d : CFSG.KC.Census.ConjDataP, suzCheckWExc suzE0 d = true :=
  Certificates.certificate15037

theorem suz_endCheck : SuzEndFactsK :=
  Certificates.certificate15038

theorem sporadicCaseOdd_Suz
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Suz :=
  sporadicCaseOdd_Suz_of_check suz_checkII.choose_spec suz_checkExc.choose_spec suz_endCheck
    (suzCentralTwoGroupOrderBound_of_checks suz_tabCheck suz_rho0Check suz_l0Check suz_l1Check
      suz_l2Check)
    (suzDoubleCoverTwoBLift_of_checks suz_tabCheck suz_rho0Check suz_rhoJ2Check suz_l0Check
      suz_l1Check suz_l2Check) h32 h33

theorem suzMultiplierSix :
    RankTwoL3Four.SuzMultiplierSix :=
  RankTwoL3Four.suzMultiplierSix_of_checks suz_tabCheck suz_rho0Check suz_l0Check suz_l1Check
    suz_l2Check

end CFSG.ComponentClassification.RankTwoSporadic.Suz

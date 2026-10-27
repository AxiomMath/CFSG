module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEnd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuCover
public import Certificates.Certificate15022
public import Certificates.Certificate15023
public import Certificates.Certificate15024
public import Certificates.Certificate15025
public import Certificates.Certificate15026

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open CFSG.Sporadic.RuSchreier

theorem ru_censusCheck :
    YCensus (ruP.subgroupOf ruP) (Cert.ExcClass ruP ruE0Sub) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩ := Certificates.certificate15022
  exact census_of_ruCheckR h

theorem ru_endCheck : RuEndFactsK :=
  Certificates.certificate15023

theorem ru_tabCheck :
    CFSG.Sporadic.Recognition.RuMultiplier.RuTabFact :=
  Certificates.certificate15024

theorem ru_rhoCheck :
    CFSG.Sporadic.Recognition.RuMultiplier.ruRhoCheck = true :=
  Certificates.certificate15025

theorem ru_l0Check :
    CFSG.Sporadic.Recognition.RuMultiplier.RuIndexK :=
  Certificates.certificate15026

theorem sporadicCaseOdd_Ru
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Ru :=
  sporadicCaseOdd_Ru_of_check ru_censusCheck ru_endCheck
    (ruCentralTwoGroupOrderBound_of_checks ru_tabCheck ru_l0Check)
    (ruDoubleCoverTwoBLift_of_checks ru_tabCheck ru_rhoCheck ru_l0Check) h32 h33

end CFSG.ComponentClassification.RankTwoSporadic.Ru

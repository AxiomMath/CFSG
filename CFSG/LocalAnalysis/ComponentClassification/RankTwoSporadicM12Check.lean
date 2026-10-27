module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12End
public import Certificates.Certificate15015
public import Certificates.Certificate15016
public import Certificates.Certificate15017

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open CFSG.ComponentClassification.Asc76 CFSG.ComponentClassification.AschbacherTheorem3

theorem m12_censusCheck :
    ∃ (sG roots : Array ℕ) (nodes : Array CFSG.KC.Census.NodeP) (cS : CFSG.KC.Census.ArrCertP)
      (wcs : Array (Array CFSG.KC.Census.ArrCertP)) (excs : List CFSG.KC.Census.ExcRefP),
    m12CheckW m12S m12W m12E0 sG roots nodes cS wcs excs = true :=
  Certificates.certificate15015

theorem m12_endCheck :
    m12EndCheck m12S m12E0 m12EndA0 m12EndLeaves m12EndL m12EndSigma m12EndC0 m12EndZ = true :=
  Certificates.certificate15016

theorem m12_overCheck : m12OverFacts m12S :=
  Certificates.certificate15017

theorem sporadicCaseOdd_M12
    (h3L : Asc76Theorem3Large) (h22 : Asc76Lemma22) (h4' : Asc76Theorem4) :
    SporadicCaseOdd .M12 := by
  obtain ⟨_, _, _, _, _, _, hc⟩ := m12_censusCheck
  exact sporadicCaseOdd_M12_of_check hc m12_endCheck m12_overCheck h3L h22 h4'

end CFSG.ComponentClassification.RankTwoSporadic.M12

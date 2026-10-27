module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2End
public import Certificates.Certificate15006
public import Certificates.Certificate15007
public import Certificates.Certificate15008

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J2End

theorem j2_checkII :
    ∃ (sG roots : Array ℕ) (nodes : Array CFSG.KC.Census.NodeP) (cS : CFSG.KC.Census.ArrCertP)
      (wcs : Array (Array CFSG.KC.Census.ArrCertP)),
    RankTwoSporadic.J2.j2CheckWII sG roots nodes cS wcs = true :=
  Certificates.certificate15006

theorem j2_checkExc :
    ∃ (sG roots : Array ℕ) (nodes : Array CFSG.KC.Census.NodeP) (cS : CFSG.KC.Census.ArrCertP)
      (wcs : Array (Array CFSG.KC.Census.ArrCertP)) (excs : List CFSG.KC.Census.ExcRefP),
    RankTwoSporadic.J2.j2CheckWExc RankTwoSporadic.J2.j2E0 sG roots nodes cS wcs excs = true :=
  Certificates.certificate15007

theorem j2_checkEnd : RankTwoSporadic.J2.j2EndCheck RankTwoSporadic.J2.j2E0 RankTwoSporadic.J2.j2EndA0 RankTwoSporadic.J2.j2EndC0 RankTwoSporadic.J2.j2EndLeaves RankTwoSporadic.J2.j2EndN0 = true :=
  Certificates.certificate15008

theorem sporadicCaseOdd_J2
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .J2 := by
  obtain ⟨_, _, _, _, _, hII⟩ := j2_checkII
  obtain ⟨_, _, _, _, _, _, hX⟩ := j2_checkExc
  exact sporadicCaseOdd_J2_of_check hII hX j2_checkEnd h32 h33

end CFSG.ComponentClassification.RankTwoSporadic.J2End

module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1
public import Certificates.Certificate15004

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J1

open CFSG.KC.Census

theorem j1_check :
    ∃ (prog : List (ℕ × ℕ)) (sG : Array ℕ) (nodes : Array FNodeP) (cS : ArrCertP),
      j1CheckW prog sG nodes cS = true :=
  Certificates.certificate15004

theorem sporadicCaseOdd_J1
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .J1 := by
  obtain ⟨_, _, _, _, h⟩ := j1_check
  exact sporadicCaseOdd_J1_of_check h h32 h33

end CFSG.ComponentClassification.RankTwoSporadic.J1

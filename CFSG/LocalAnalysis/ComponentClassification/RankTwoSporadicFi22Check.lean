module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi22
public import CFSG.Certificates.Kernel.Census.PidProof
public import Certificates.Certificate15010

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi22

open CFSG.KC.Census CFSG.RankThree.Native

theorem sporadicCaseOdd_Fi22
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Fi22 := by
  obtain ⟨_, _, _, _, hs, hw, hc, hII, h17, hf, hl⟩ := Certificates.certificate15010
  refine sporadicCaseOdd_Fi22_of_check (fun P hP hv hx => ?_) (fun P hP hv hx => ?_) hc hII h17
    hf hl h32 h33
  · exact (fi22InPT_iff _ _ (rep_of_validA (validA_unpackP_proved (by norm_num) (by norm_num) hP hv))).1
      (hs P hx)
  · exact (fi22InRT_iff _ _ (rep_of_validA (validA_unpackP_proved (by norm_num) (by norm_num) hP hv))).1
      (hw P hx)

end CFSG.ComponentClassification.RankTwoSporadic.Fi22

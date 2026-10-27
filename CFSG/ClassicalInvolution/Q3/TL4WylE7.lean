module

public import CFSG.ClassicalInvolution.Q3.TL4WylE2
public import CFSG.ClassicalInvolution.Q3.TL4WylE5
public import CFSG.ClassicalInvolution.Q3.TL4WylE6
public import CFSG.ClassicalInvolution.Q3.TL4ConnBend

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

section Cit3


theorem tightSecFrameR_three_of {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (h4 : Thm4RBelow 3 n) : TightSecFrameR 3 n :=
  tightSecFrameR_of_plus hA hP h4 secIdE2Frame_proved secIdE4Frame_proved secIdLieFrame_proved

theorem tightW2CaseBR_three_of {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (h4 : Thm4RBelow 3 n) (hF : TightAlphaFrameR 3 n) (hH : TightHyp51TriR 3 n) :
    TightW2CaseBR 3 n :=
  tightW2CaseBR_of tightBenderEndR hF hH h4 (tightSecFrameR_three_of hA hP h4)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

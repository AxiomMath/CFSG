module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian

public section

namespace CFSG.CGT.Timmesfeld75

theorem goldschmidt1974_of_milestone :
    Goldschmidt1974 :=
  fun X _ _ S A hAS hAab hclosed => by
    have h := CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian X S A hAS hAab hclosed
    exact h

end CFSG.CGT.Timmesfeld75

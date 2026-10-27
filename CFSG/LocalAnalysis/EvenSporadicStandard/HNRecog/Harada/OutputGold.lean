module

public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210ThmA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

theorem goldschmidtTheoremA
    : GoldschmidtTheoremA := fun X _ _ S A hAS hAab hclosed =>
  CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian X S A hAS hAab hclosed

end CFSG.EvenSporadicStandard.HNRecog.Harada

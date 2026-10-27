module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian

public section

namespace CFSG.ComponentClassification.Asc76X

open CFSG.ComponentClassification.Asc76

theorem hallFusionThm32_of_core (hcore : Hall32Core) : HallFusionThm32 :=
  hallFusionThm32_of CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian hcore

end CFSG.ComponentClassification.Asc76X

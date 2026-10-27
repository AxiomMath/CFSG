module

public import CFSG.HardMathSupport.Solomon.Coordinator.SignalizerFunctor
public import CFSG.Milestones.CL_LIT_signalizer_functor_theorem

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem signalizerFunctorTheoremK_holds :
    SignalizerFunctorTheoremK :=
  fun G _ _ p hp k hk A hA hrank Θ hcent hcop hinv hbal hK =>
    CFSG.Milestones.cl_lit_signalizer_functor_theorem_1 G p hp k hk A hA hrank Θ hcent hcop hinv
      hbal hK

end CFSG.HardMathSupport.Solomon.Coordinator

module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.DiagLinear
public import CFSG.HardMathSupport.Malle.Proving.OuterHeisCoreFour

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

theorem coverThreeNoInnerDiagLinear : CoverThreeNoInnerDiagLinear :=
  coverThreeNoInnerDiagLinear_of_four
    (coverThreeNoInnerDiagLinearFour_of_core fun _ _ _ hF ω α hω hω1 hα hαc =>
      CFSG.HardMathSupport.Malle.Proving.outerHeisCoreFour hF ω α hω hω1 hα hαc)

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

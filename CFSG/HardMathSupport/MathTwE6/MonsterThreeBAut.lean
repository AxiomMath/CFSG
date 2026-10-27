module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.MathTwE6.M3BIrrCheck
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.AltDown

public section

namespace CFSG.HardMathSupport.MathTwE6.M3BIrr

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.YS08

theorem finite_mulAut (X : Type*) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun φ : MulAut X => (φ : X → X)) DFunLike.coe_injective

end CFSG.HardMathSupport.MathTwE6.M3BIrr

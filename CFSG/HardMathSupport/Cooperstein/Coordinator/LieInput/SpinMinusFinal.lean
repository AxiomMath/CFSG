module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusLevi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusDBlock

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput


theorem orthMinusLeviOb : OrthMinusLeviOb :=
  orthMinusLeviOb_of_lastBlock fun n {F} _ _ _ {b c} hirr _ a k h hk =>
    ⟨blkEquivMinus h hirr hk⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

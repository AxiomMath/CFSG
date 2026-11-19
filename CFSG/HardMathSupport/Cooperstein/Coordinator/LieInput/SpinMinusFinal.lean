module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusLevi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusDBlock

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput


theorem orthMinusLeviOb : OrthMinusLeviOb :=
  orthMinusLeviOb_of_lastBlock fun _n {_F} _ _ _ {_b _c} hirr _ _a _k h hk =>
    ⟨blkEquivMinus h hirr hk⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

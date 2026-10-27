module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Reduction
public import CFSG.HardMathSupport.Timmesfeld.Proving.MapGLAPPrimeCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance

theorem deltaOfLocalBalance_proved :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.DeltaOfLocalBalance :=
  deltaOfLocalBalance_of_H1 (by
    intro X Z _ _ _ φ hφ p hp Q hQ
    exact CFSG.HardMathSupport.Timmesfeld.Proving.map_glaPPrimeCoreOf_centralizer_le φ hφ hp hQ)

end CFSG.HardMathSupport.Timmesfeld.Balance

module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPAll
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4B2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

set_option linter.unusedSectionVars false


theorem lieCompsOn_exceptional_of_two_residuals {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hD : ExcRationalLieTypesOuterDP p) (hF : ExcRationalLieTypesF4SmallP p) :
    LieCompsOn p .exceptional :=
  lieCompsOn_exceptional_of_residuals hp hp5 hD
    (excRationalLieTypesF4P_of_small hp (by omega) hF) (trialityFieldExportP hp hp5)

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

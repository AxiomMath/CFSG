module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsP
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

set_option linter.unusedSectionVars false


theorem lieCompsOn_exceptional_of_residuals {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hD : ExcRationalLieTypesOuterDP p) (hF : ExcRationalLieTypesF4P p)
    (hT : TrialityFieldExportP p) : LieCompsOn p .exceptional :=
  lieCompsOn_exceptional hp hp5 (excRationalLieTypesP_of_residuals hp (by omega) hD hF) hT

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

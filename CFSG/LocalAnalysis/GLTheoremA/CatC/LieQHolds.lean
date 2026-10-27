module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddTop
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieQ

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section KDCharPHolds

set_option linter.unusedSectionVars false

theorem kdCharP_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : KDCharP p :=
  kdCharP_of_lieQConstrainedInner hp
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrainedInner_odd hp hp2)

end KDCharPHolds

end CFSG.LocalAnalysis.GLTheoremA

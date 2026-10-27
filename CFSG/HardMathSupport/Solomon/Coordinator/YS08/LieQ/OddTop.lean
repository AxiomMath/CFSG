module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddL28

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

set_option linter.unusedSectionVars false

section Top


theorem lieQConstrainedInner_three_holds : LieQConstrainedInner 3 :=
  lieQConstrainedInner_three psl28Inner

theorem lieQConstrainedInner_odd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : LieQConstrainedInner q := by
  by_cases h3 : q = 3
  · subst h3
    exact lieQConstrainedInner_three_holds
  · exact lieQConstrainedInner_of_ne_three hq hq2 h3

end Top

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

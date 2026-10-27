module

public import CFSG.ClassicalInvolution.Q3.Q3OTSq
public import CFSG.ClassicalInvolution.Q3.Q3OTD4Sq

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77


theorem twinSqAlpha3_odd' (n : ℕ) (_hn : 3 ≤ n)
    (hadm : StatedLieAdmissible .POmegaOdd n 3 1) : TwinSqAlpha 3 1 .POmegaOdd n :=
  twinSqAlpha3_odd hadm

theorem twinSqAlpha3_plus' (n : ℕ) (hn : 4 ≤ n)
    (hadm : StatedLieAdmissible .POmegaPlus n 3 1) : TwinSqAlpha 3 1 .POmegaPlus n := by
  rcases Nat.lt_or_ge n 5 with h | h
  · obtain rfl : n = 4 := by omega
    exact twinSqAlpha3_d4
  · exact twinSqAlpha3_plus hadm h

theorem twinSqAlpha3_minus' (n : ℕ) (_hn : 4 ≤ n)
    (hadm : StatedLieAdmissible .POmegaMinus n 3 1) : TwinSqAlpha 3 1 .POmegaMinus n :=
  twinSqAlpha3_minus hadm

end CFSG.ClassicalInvolution.Q3.Q3OT

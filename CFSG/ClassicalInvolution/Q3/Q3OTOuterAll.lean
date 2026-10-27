module

public import CFSG.ClassicalInvolution.Q3.Q3OTOuter
public import CFSG.ClassicalInvolution.Q3.Q3OTD4Outer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77


theorem twinOuterAlpha3_odd' (n : ℕ) (_hn : 3 ≤ n)
    (hadm : StatedLieAdmissible .POmegaOdd n 3 1) : TwinOuterAlpha 3 1 .POmegaOdd n :=
  twinOuterAlpha3_odd hadm

theorem twinOuterAlpha3_plus' (n : ℕ) (hn : 4 ≤ n)
    (hadm : StatedLieAdmissible .POmegaPlus n 3 1) : TwinOuterAlpha 3 1 .POmegaPlus n := by
  rcases Nat.lt_or_ge n 5 with h | h
  · obtain rfl : n = 4 := by omega
    exact twinOuterAlpha3_d4
  · exact twinOuterAlpha3_plus hadm h

theorem twinOuterAlpha3_minus' (n : ℕ) (_hn : 4 ≤ n)
    (hadm : StatedLieAdmissible .POmegaMinus n 3 1) : TwinOuterAlpha 3 1 .POmegaMinus n :=
  twinOuterAlpha3_minus hadm

end CFSG.ClassicalInvolution.Q3.Q3OT

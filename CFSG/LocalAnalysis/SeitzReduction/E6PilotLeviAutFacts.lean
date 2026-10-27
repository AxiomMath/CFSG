module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutZ
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotPositionFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem factF5E6_of_four_le (hq : 4 ≤ Nat.card K) : FactF5E6 K :=
  fun κ κ' ι => exists_map_eq_map_conj_f5Levi hq κ κ' ι

end CFSG.SeitzReduction.E6Pilot

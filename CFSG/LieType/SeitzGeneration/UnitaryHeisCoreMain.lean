module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreProof
public import CFSG.LieType.SeitzGeneration.HeisSmallCases

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LieType.SeitzGeneration.HeisSmall

theorem unitaryHeisCore :
    UnitaryHeisCore :=
  unitaryHeisCore_of_finite_cases
    (fun _ _ _ _ h hq ω hω => heisB12_le_heisClosure_q5 h (by rw [hq]; norm_num) hq hω)
    (fun _ _ _ _ h hq ω hω => heisB12_le_heisClosure_q8 h (by rw [hq]; norm_num) hq hω)
    (fun _ _ _ _ h hq ω hω => heisB12_le_heisClosure_q11 h (by rw [hq]; norm_num) hq hω)

end CFSG.LieType.SeitzGeneration

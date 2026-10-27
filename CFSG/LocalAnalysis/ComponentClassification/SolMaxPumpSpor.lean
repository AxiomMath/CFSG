module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporOrd
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporComp
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporFi
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporM
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporHS
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporRes
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpReduce

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG

theorem altPumpSporadicClause_of_inputs
    (hSuz : SuzOuterComponentsInput)
    (hON : ONOuterComponentsInput) : AltPumpSporadicClause := by
  intro S _ _ _ hna s hs hS σ P h hex m hm hm7 hP
  have key : AltPumpSporClauseFor s := by
    cases s with
    | M11 => exact altPumpSpor_M11
    | M12 => exact altPumpSpor_M12
    | M22 => exact altPumpSpor_M22
    | M23 => exact altPumpSpor_M23
    | M24 => exact altPumpSpor_M24
    | J1 => exact altPumpSpor_J1
    | J2 => exact altPumpSpor_J2
    | J3 => exact altPumpSpor_J3
    | J4 => exact altPumpSpor_J4
    | Co1 => exact altPumpSpor_Co1
    | Co2 => exact altPumpSpor_Co2
    | Co3 => exact altPumpSpor_Co3
    | Fi22 => exact altPumpSpor_Fi22
    | Fi23 => exact altPumpSpor_Fi23
    | Fi24Prime => exact altPumpSpor_Fi24Prime
    | HS => exact altPumpSpor_HS
    | McL => exact altPumpSpor_McL
    | He => exact absurd rfl hs
    | Ru => exact altPumpSpor_Ru
    | Suz => exact altPumpSpor_Suz hSuz
    | ONan => exact altPumpSpor_ONan hON
    | HN => exact altPumpSpor_HN
    | Ly => exact altPumpSpor_Ly
    | Th => exact altPumpSpor_Th
    | B => exact altPumpSpor_B
    | M => exact altPumpSpor_M
  exact key S hna hS σ P h hex m hm hm7 hP

end CFSG.ComponentClassification.SolMax

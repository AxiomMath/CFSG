module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporOrd
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporComp
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporCompB
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporFi
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporB
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporM
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporHS
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporRes
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpDefs

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG.ComponentClassification.SolMax

open CFSG

theorem evenAltPumpSporadicClause_of_inputs
    (hSuz : SuzOuterComponentsInput)
    (hON : ONOuterComponentsInput) : EvenAltPumpSporadicClause := by
  intro S _ _ _ hna s hs hsHN hS σ P h hex m hm hm10 hP
  have key : EvenPumpSporClauseFor s := by
    cases s with
    | M11 => exact evenPumpSpor_M11
    | M12 => exact evenPumpSpor_M12
    | M22 => exact evenPumpSpor_M22
    | M23 => exact evenPumpSpor_M23
    | M24 => exact evenPumpSpor_M24
    | J1 => exact evenPumpSpor_J1
    | J2 => exact evenPumpSpor_J2
    | J3 => exact evenPumpSpor_J3
    | J4 => exact evenPumpSpor_J4
    | Co1 => exact evenPumpSpor_Co1
    | Co2 => exact evenPumpSpor_Co2
    | Co3 => exact evenPumpSpor_Co3
    | Fi22 => exact evenPumpSpor_Fi22
    | Fi23 => exact evenPumpSpor_Fi23
    | Fi24Prime => exact evenPumpSpor_Fi24Prime
    | HS => exact evenPumpSpor_HS
    | McL => exact evenPumpSpor_McL
    | He => exact absurd rfl hs
    | Ru => exact evenPumpSpor_Ru
    | Suz => exact evenPumpSpor_Suz hSuz
    | ONan => exact evenPumpSpor_ONan hON
    | HN => exact absurd rfl hsHN
    | Ly => exact evenPumpSpor_Ly
    | Th => exact evenPumpSpor_Th
    | B => exact evenPumpSpor_B
    | M => exact evenPumpSpor_M
  exact key S hna hS σ P h hex m hm hm10 hP

end CFSG.ComponentClassification.EvenPump

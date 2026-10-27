module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporComp
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporHe
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporJ3
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporHS
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporTwo

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG

theorem fivePump_spor_other
    (s : TauCeti.SporadicName) (hs : s ≠ .J1 ∧ s ≠ .J2 ∧ s ≠ .M12) :
    FivePumpSporClause s := by
  apply Spor.fivePumpSporClause_of_clauseFor
  cases s with
  | M11 => exact Spor.fiveSpor_M11
  | M12 => exact absurd rfl hs.2.2
  | M22 => exact Spor.fiveSpor_M22
  | M23 => exact Spor.fiveSpor_M23
  | M24 => exact Spor.fiveSpor_M24
  | J1 => exact absurd rfl hs.1
  | J2 => exact absurd rfl hs.2.1
  | J3 => exact Spor.fiveSpor_J3
  | J4 => exact Spor.fiveSpor_J4
  | Co1 => exact Spor.fiveSpor_Co1
  | Co2 => exact Spor.fiveSpor_Co2
  | Co3 => exact Spor.fiveSpor_Co3
  | Fi22 => exact Spor.fiveSpor_Fi22
  | Fi23 => exact Spor.fiveSpor_Fi23
  | Fi24Prime => exact Spor.fiveSpor_Fi24Prime
  | HS => exact Spor.fiveSpor_HS
  | McL => exact Spor.fiveSpor_McL
  | He => exact Spor.fiveSpor_He
  | Ru => exact Spor.fiveSpor_Ru
  | Suz => exact Spor.fiveSpor_Suz
  | ONan => exact Spor.fiveSpor_ONan
  | HN => exact Spor.fiveSpor_HN
  | Ly => exact Spor.fiveSpor_Ly
  | Th => exact Spor.fiveSpor_Th
  | B => exact Spor.fiveSpor_B
  | M => exact Spor.fiveSpor_M

theorem fiveTwoLayer_spor
    (s : TauCeti.SporadicName) : FiveTwoLayerSporClause s := by
  cases s with
  | M11 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_M11
  | M12 => exact Spor.fiveTwoLayerSpor_M12
  | M22 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_M22
  | M23 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_M23
  | M24 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_M24
  | J1 => exact Spor.fiveTwoLayerSpor_J1
  | J2 => exact Spor.fiveTwoLayerSpor_J2
  | J3 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_J3
  | J4 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_J4
  | Co1 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_Co1
  | Co2 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_Co2
  | Co3 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_Co3
  | Fi22 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_Fi22
  | Fi23 => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_Fi23
  | Fi24Prime => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_Fi24Prime
  | HS => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_HS
  | McL => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_McL
  | He => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_He
  | Ru => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_Ru
  | Suz => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_Suz
  | ONan => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_ONan
  | HN => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_HN
  | Ly => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_Ly
  | Th => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_Th
  | B => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_B
  | M => exact Spor.fiveTwoLayerSporClause_of_clauseFor Spor.fiveSpor_M

end CFSG.ComponentClassification.SolMax.FiveCat

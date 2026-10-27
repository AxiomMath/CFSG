module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSpor516A
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSpor516B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSpor516Baby
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSpor516M

public section

namespace CFSG.ComponentClassification.SolMax.Spor516

open CFSG CFSG.Blueprint CFSG.ComponentClassification.GSThmB

theorem cf516SporRow
    : CF516SporRow := by
  intro S _ _ s ⟨e⟩
  cases s with
  | M11 => exact leafAt_M11 e
  | M12 => exact leafAt_M12 e
  | M22 => exact leafAt_M22 e
  | M23 => exact leafAt_M23 e
  | M24 => exact leafAt_M24 e
  | J1 => exact leafAt_J1 e
  | J2 => exact leafAt_J2 e
  | J3 => exact leafAt_J3 e
  | J4 => exact leafAt_J4 e
  | Co1 => exact leafAt_Co1 e
  | Co2 => exact leafAt_Co2 e
  | Co3 => exact leafAt_Co3 e
  | Fi22 => exact leafAt_Fi22 e
  | Fi23 => exact leafAt_Fi23 e
  | Fi24Prime => exact leafAt_Fi24Prime e
  | HS => exact leafAt_HS e
  | McL => exact leafAt_McL e
  | He => exact leafAt_He e
  | Ru => exact leafAt_Ru e
  | Suz => exact leafAt_Suz e
  | ONan => exact leafAt_ONan e
  | HN => exact leafAt_HN e
  | Ly => exact leafAt_Ly e
  | Th => exact leafAt_Th e
  | B => exact leafAt_B e
  | M => exact leafAt_M e

end CFSG.ComponentClassification.SolMax.Spor516

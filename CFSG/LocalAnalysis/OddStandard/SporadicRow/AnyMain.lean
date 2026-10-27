module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.AnyMathieuRudvalis
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.AnyHSMcLHe
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.AnySuzONCoFi
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.AnyHNLyThJ4
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.AnyBabyMonster

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.Blueprint T1.SporRow


theorem T1.SporRow.sporOddCompsAny_of (s : TauCeti.SporadicName)
    (hs : s ≠ .M11 ∧ s ≠ .M12 ∧ s ≠ .J1 ∧ s ≠ .J2 ∧ s ≠ .J3 ∧ s ≠ .HS) : SporOddCompsAny s := by
  cases s with
  | M11 => exact absurd rfl hs.1
  | M12 => exact absurd rfl hs.2.1
  | J1 => exact absurd rfl hs.2.2.1
  | J2 => exact absurd rfl hs.2.2.2.1
  | J3 => exact absurd rfl hs.2.2.2.2.1
  | HS => exact absurd rfl hs.2.2.2.2.2
  | M22 => exact sporOddCompsAny_M22
  | M23 => exact sporOddCompsAny_M23
  | M24 => exact sporOddCompsAny_M24
  | Ru => exact sporOddCompsAny_Ru
  | McL => exact sporOddCompsAny_McL
  | He => exact sporOddCompsAny_He
  | Suz => exact sporOddCompsAny_Suz
  | ONan => exact sporOddCompsAny_ONan
  | Co1 => exact sporOddCompsAny_Co1
  | Co2 => exact sporOddCompsAny_Co2
  | Co3 => exact sporOddCompsAny_Co3
  | Fi22 => exact sporOddCompsAny_Fi22
  | Fi23 => exact sporOddCompsAny_Fi23
  | Fi24Prime => exact sporOddCompsAny_Fi24Prime
  | HN => exact sporOddCompsAny_HN
  | Ly => exact sporOddCompsAny_Ly
  | Th => exact sporOddCompsAny_Th
  | J4 => exact sporOddCompsAny_J4
  | B => exact sporOddCompsAny_B
  | M => exact sporOddCompsAny_M

end CFSG.ComponentClassification.HarrisLit

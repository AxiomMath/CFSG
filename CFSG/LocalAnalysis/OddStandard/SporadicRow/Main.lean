module

public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Simple
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.MTypeSchur
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.HSMcLHe
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.MathieuRudvalis
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.SuzONCoFi
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.HNLyThJ4
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.BabyMonster
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.J1
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.J2
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.J3
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.M12
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spor

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.Blueprint T1.SporRow


theorem T1.SporRow.sporOddComps_of (s : TauCeti.SporadicName) (hs : s ≠ .M11) : SporOddComps s := by
  cases s with
  | M11 => exact absurd rfl hs
  | M12 => exact sporOddComps_M12
  | M22 => exact sporOddComps_M22
  | M23 => exact sporOddComps_M23
  | M24 => exact sporOddComps_M24
  | J1 => exact sporOddComps_J1
  | J2 => exact sporOddComps_J2
  | J3 => exact sporOddComps_J3
  | J4 => exact sporOddComps_J4
  | HS => exact sporOddComps_HS
  | McL => exact sporOddComps_McL
  | He => exact sporOddComps_He
  | Ru => exact sporOddComps_Ru
  | Suz => exact sporOddComps_Suz
  | ONan => exact sporOddComps_ONan
  | Co1 => exact sporOddComps_Co1
  | Co2 => exact sporOddComps_Co2
  | Co3 => exact sporOddComps_Co3
  | Fi22 => exact sporOddComps_Fi22
  | Fi23 => exact sporOddComps_Fi23
  | Fi24Prime => exact sporOddComps_Fi24Prime
  | HN => exact sporOddComps_HN
  | Ly => exact sporOddComps_Ly
  | Th => exact sporOddComps_Th
  | B => exact sporOddComps_B
  | M => exact sporOddComps_M

theorem T1.SporRow.not_oddLieOrder_of_sporadic {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hS : NativeSporadic.SporadicRep S)
    (hM11 : ¬ Nonempty (S ≃* ↥NativeSporadic.M11)) {t : S} (ht : orderOf t = 2) {L : Subgroup S}
    (hL : IsTwoComponentIn L (centralizer {t})) (htL : t ∈ L) :
    ¬ OddLieOrder (Nat.card (↥L ⧸ Open.fusionZStar ↥L)) := by
  obtain ⟨s, ⟨e⟩⟩ := hS
  have hs : s ≠ .M11 := by
    rintro rfl
    exact hM11 ⟨e⟩
  exact not_oddLieOrder_card_quotient_fusionZStar ((sporT1Data_of s hs).oddCore S hna e t ht) hL htL
    (sporOddComps_of s hs S hna e t ht)


theorem harris82SporadicRow : Harris82SporadicRow := by
  intro S _ _ _ hna hS hM11 t ht L hL htL p hp hp2 hM
  exact not_oddLieOrder_of_sporadic hna hS hM11 ht hL htL
    (oddLieOrder_of_isMTypeSchur hp hp2 hL.2.2.1 hM)

end CFSG.ComponentClassification.HarrisLit

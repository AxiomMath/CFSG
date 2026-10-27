module

public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTL4Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTRankLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.CoverModel
public import CFSG.Sporadic.Recognition.HNMultiplierCert
public import CFSG.Sporadic.Recognition.McLMultiplierCert

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpT

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier
  CFSG.LocalAnalysis.ComponentInitial CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

theorem kgPumpRank_proved :
    KGPumpRank := by
  intro K _ _ hK hZ hP
  rcases hP with ⟨k, hk, ⟨e⟩⟩ | hHS | hMcL | hHN | ⟨i, hi, hL⟩
  · exact le_trans (by norm_num) (three_le_pRank_alt_cover (n := 2 * k) (by omega) e)
  · obtain ⟨e₀⟩ := hHS
    obtain ⟨a₁, a₂, a₃, n, hE8, -, -⟩ := EvenSporadicStandard.TwoHS.cover_datum
    exact le_trans (by norm_num) (three_le_pRank_of_e8Datum_quotient
      ((e₀ : (K ⧸ center K) ≃* CFSG.Blueprint.NativeSporadic.HS).trans hsPermEquiv) hE8)
  · obtain ⟨e⟩ := hMcL
    exact two_le_pRank_of_isQuasisimple_of_odd_center hK (Odd.of_dvd_nat (by decide)
      (Sporadic.Recognition.McLMultiplier.card_center_dvd_three_of_certificate hK.1 e))
  · obtain ⟨e⟩ := hHN
    have hbot := Sporadic.Recognition.HNMultiplier.center_eq_bot_of_certificate hK.1 hZ e
    exact two_le_pRank_of_isQuasisimple_of_odd_center hK
      (by rw [hbot, Subgroup.card_bot]; exact odd_one)
  · have hf : 2 ≤ 2 ^ i := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    have hbot := center_eq_bot_of_psl_four hK hZ hf hL
    exact two_le_pRank_of_isQuasisimple_of_odd_center hK
      (by rw [hbot, Subgroup.card_bot]; exact odd_one)

end CFSG.EvenSporadicStandard.HSStd.PumpT

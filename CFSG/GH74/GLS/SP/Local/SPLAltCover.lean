module

public import CFSG.GH74.GLS.SP.Local.SPLAltCoverC
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU13.TA

theorem stableL34Cover : StableL34Cover := by
  intro X _ _ z t A T₁ L ctx hL _ h34 hexp
  obtain ⟨-, -, -, -, -, -, -, -, -, hAZ⟩ := ctx.altCover_A_facts
  have hcardQ : Nat.card (↥L ⧸ center ↥L) = 20160 := by
    rw [card_of_lieModel_PSL (by norm_num) h34]
    decide
  have hAdvd : Nat.card ↥A ∣ 19958400 := by
    have h := altCover_card_dvd_of_ker_le_center hL.A_le hAZ (QuotientGroup.mk' (center ↥L))
      (by rw [QuotientGroup.ker_mk'])
    rw [hcardQ] at h
    exact h.trans (by norm_num)
  have h4 : 4 ∣ Nat.card ↥(center ↥L) := hexp ▸ Group.exponent_dvd_nat_card
  have h256 : 2 ^ 8 ∣ Nat.card ↥L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L), hcardQ,
      show (2 : ℕ) ^ 8 = 2 ^ 6 * 4 by norm_num]
    exact mul_dvd_mul (by norm_num) h4
  obtain ⟨P, hP, hPcard⟩ := altCover_exists_twoSubgroup_of_pow_dvd L h256
  have := ctx.altCover_card_le_one_two_eight hAdvd hP
  norm_num at hPcard
  omega

theorem stableDoubleCoverAlt : StableDoubleCoverAlt := by
  intro X _ _ z t A T₁ L ctx hL ⟨n, hn8, hn11, hD⟩
  obtain ⟨q, -, -, hqodd, hq5, -, -, -, hAcard, hAZ⟩ := ctx.altCover_A_facts
  by_cases hzL : z ∈ L
  · obtain ⟨π, hπ⟩ := TwoCover.exists_of_isTwoAlt (H := ↥L) ⟨hD.1, inferInstance, hD.2.1, hD.2.2⟩
    exact altCover_false_of_mem hn8 hn11 hπ hL.A_le hAZ ctx.A_cen ctx.z_sq ctx.z_ne_one hzL
      hL.moves hqodd hq5 hAcard
  · exact altCover_false_of_not_mem ctx hL hn8 hn11 hD hzL

end CFSG.GH74.GLS.SP.Local

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OStep5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5o_centerIn_eq_zpowers {G : Type} [Group G] [Finite G] (h52b : Asc82Lemma52b)
    {t : G} {L : Subgroup G} (hs : Sec5Setting G t L) (hO : oddCoreIn L = ⊥) :
    centerIn L = zpowers t := by
  have hΩ : IsOm6Z2 L := hs.isOm6Z2
  have ht : t ∈ centerIn L := sec5o_t_mem_centerIn h52b hs
  apply le_antisymm
  · intro x hx
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hyc : x ^ (2 ^ k) ∈ centerIn L := (centerIn L).pow_mem hx _
    have hyord : orderOf (x ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (by positivity) (hkm ▸ dvd_mul_right _ _), hkm,
        Nat.mul_div_cancel_left _ (by positivity)]
    obtain ⟨hyL, hycomm⟩ := sec5_mem_centerIn_iff.mp hyc
    have hNL : zpowers (x ^ (2 ^ k)) ≤ L := Subgroup.zpowers_le.mpr hyL
    have hnormal : ((zpowers (x ^ (2 ^ k))).subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNL]
      intro l hl
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hc : Commute (x ^ (2 ^ k)) l := hycomm l hl
      exact (hc.zpow_left j).eq
    have hodd : Odd (Nat.card (zpowers (x ^ (2 ^ k)))) := by
      rw [Nat.card_zpowers, hyord]
      exact hm
    have hle := le_oddCoreIn_of_normal hNL hnormal hodd
    rw [hO] at hle
    have hy1 : x ^ (2 ^ k) = 1 :=
      Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
    have hm1 : m = 1 := by rw [← hyord, hy1, orderOf_one]
    exact sec5_mem_zpowers_of_twoElement hΩ ht hs.involution hx
      ⟨k, by rw [hkm, hm1, mul_one]⟩
  · exact Subgroup.zpowers_le.mpr ht

theorem asc82Lemma512b_of (h34a : Asc82Lemma34a) (hy : Sec5B59Hyp) (h52a : Asc82Lemma52a)
    (l58d : Asc82Lemma58d) (f59 : Asc82Fact59) (f510 : Asc82Fact510)
    (hP : Asc82FactPockets6) (hQ : Asc82FactQCent6) (hF : Asc82FactFrame6)
    (hZ : Asc82FactOutZeta6) : Asc82Lemma512b := by
  intro G _ _ t L S z r B A hR
  exact sec5o_centerIn_eq_zpowers hy.h52b hR.toSec5Ctx.toSec5Setting
    (sec5_oddCore_trivial h34a hy h52a l58d f59 f510 hP hQ hF hZ hR)

end CFSG.OddStandard.SmallF3.Omega

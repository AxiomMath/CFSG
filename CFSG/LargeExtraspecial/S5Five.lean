module

public import CFSG.LargeExtraspecial.S5Four
public import CFSG.LargeExtraspecial.S5OneMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup CFSG.LargeExtraspecial.S4 CFSG.Open CFSG.ComponentClassification

universe u

theorem timmesfeldOddCore_normal (K : Type*) [Group K] : (timmesfeldOddCore K).Normal :=
  CFSG.oddCore_normal K

theorem odd_card_timmesfeldOddCore (K : Type*) [Group K] [Finite K] :
    Odd (Nat.card (timmesfeldOddCore K)) :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := K)

theorem le_timmesfeldOddCore {K : Type*} [Group K] {N : Subgroup K} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ timmesfeldOddCore K :=
  le_sSup ⟨hN, hodd⟩

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_oddCore_dvd_three (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (hn : 4 < S.width) : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 := by
  have hON := timmesfeldOddCore_normal S.Mbar
  have hodd := odd_card_timmesfeldOddCore S.Mbar
  have hcard : Nat.card ((timmesfeldOddCore S.Mbar).map S.Mbar.subtype) =
      Nat.card (timmesfeldOddCore S.Mbar) := card_map_of_injective S.Mbar.subtype_injective
  by_cases hbot : (timmesfeldOddCore S.Mbar).map S.Mbar.subtype = ⊥
  · rw [← hcard, hbot, card_bot]
    exact one_dvd _
  · have h3 := timmesfeld_5_4 H hNo C hn (map_subtype_le _) (hcard ▸ hodd) hbot fun s hs x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨⟨s, S.Lbar_le_Mbar g hs⟩ * y * (⟨s, S.Lbar_le_Mbar g hs⟩ : S.Mbar)⁻¹,
        hON.conj_mem y hy _, rfl⟩
    rw [← hcard, h3]

theorem fitting_le_oddCore (S : Setting G) :
    timmesfeldFitting S.Mbar ≤ timmesfeldOddCore S.Mbar := by
  change Fitting.subgroup S.Mbar ≤ _
  rw [PrimeCore.fitting_eq_join]
  refine iSup_le fun ⟨p, hp⟩ => ?_
  show PrimeCore.subgroup p S.Mbar ≤ _
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    have hN := PrimeCore.normal 2 S.Mbar
    have hP := PrimeCore.isPGroup 2 S.Mbar
    have e : ((PrimeCore.subgroup 2 S.Mbar).map S.Mbar.subtype).subgroupOf S.Mbar =
        PrimeCore.subgroup 2 S.Mbar :=
      comap_map_eq_self_of_injective S.Mbar.subtype_injective _
    have hsub : IsSubnormal ((PrimeCore.subgroup 2 S.Mbar).map S.Mbar.subtype) S.Mbar :=
      CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf (map_subtype_le _)
        (by rw [e]; exact hN)
    have h0 := eq_bot_of_isSubnormal_Mbar S hsub (hP.map S.Mbar.subtype)
    rw [(map_eq_bot_iff_of_injective _ S.Mbar.subtype_injective).mp h0]
    exact bot_le
  · refine le_timmesfeldOddCore (PrimeCore.normal p S.Mbar) ?_
    obtain ⟨k, hk⟩ := (PrimeCore.isPGroup p S.Mbar).exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow

theorem timmesfeldLayer_ne_bot (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (hn : 4 < S.width) : timmesfeldLayer S.Mbar ≠ ⊥ := by
  intro hE
  have hFS : GeneralizedFitting.subgroup S.Mbar ≤ timmesfeldOddCore S.Mbar := by
    change Fitting.subgroup S.Mbar ⊔ Layer.subgroup S.Mbar ≤ _
    have hE' : Layer.subgroup S.Mbar = ⊥ := hE
    rw [hE', sup_bot_eq]
    exact fitting_le_oddCore S
  have h3 : Nat.card (GeneralizedFitting.subgroup S.Mbar) ∣ 3 :=
    (card_dvd_of_le hFS).trans (card_oddCore_dvd_three H hNo C hn)
  have hBender := GeneralizedFitting.centralizer_le S.Mbar
  have hA2 : ∀ s ∈ S.Lbar g, s * s = 1 := fun s hs => S4.mul_self_of_mem_Lbar S H.conj_mem hs
  have key : ∀ t ∈ S.Lbar g, t ≠ 1 → ∀ hM : t ∈ S.Mbar,
      (⟨t, hM⟩ : S.Mbar) ∉ centralizer (GeneralizedFitting.subgroup S.Mbar : Set S.Mbar) := by
    intro t htL ht1 hM hC
    have hF := hBender hC
    have hdvd3 : orderOf (⟨t, hM⟩ : S.Mbar) ∣ 3 :=
      (Subgroup.orderOf_dvd_natCard _ hF).trans h3
    have h2 : (⟨t, hM⟩ : S.Mbar) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]
      exact hA2 t htL)
    have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) hdvd3
    rw [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    exact ht1 (congrArg Subtype.val hdvd)
  by_cases hbot : GeneralizedFitting.subgroup S.Mbar = ⊥
  · obtain ⟨t, htL, ht1⟩ : ∃ t ∈ S.Lbar g, t ≠ 1 := by
      have h16 := sixteen_le_card_Lbar C hn
      by_contra hcon
      push Not at hcon
      have hL : S.Lbar g = ⊥ := (eq_bot_iff_forall _).mpr hcon
      rw [hL, card_bot] at h16
      omega
    refine key t htL ht1 (S.Lbar_le_Mbar g htL) ?_
    rw [mem_centralizer_iff, hbot]
    intro y hy
    rw [show y = 1 from hy, one_mul, mul_one]
  · obtain ⟨⟨y, hyF⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hcard3 : Nat.card (GeneralizedFitting.subgroup S.Mbar) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
      · exact absurd (card_eq_one.mp h) hbot
      · exact h
    have hyord : orderOf y = 3 := by
      have hdvd : orderOf y ∣ 3 := hcard3 ▸ Subgroup.orderOf_dvd_natCard _ hyF
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy1'
      · exact h
    have hzF : zpowers y = GeneralizedFitting.subgroup S.Mbar :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyF) (by rw [Nat.card_zpowers, hyord, hcard3])
    have hyord' : orderOf (y : S.O) = 3 ^ 1 := by rw [Subgroup.orderOf_coe, hyord, pow_one]
    have hinv : ∀ s ∈ S.Lbar g, s * (y : S.O) * s⁻¹ ∈ zpowers (y : S.O) := by
      intro s hs
      have h1 : (⟨s, S.Lbar_le_Mbar g hs⟩ : S.Mbar) * y * (⟨s, S.Lbar_le_Mbar g hs⟩ : S.Mbar)⁻¹ ∈
          zpowers y := hzF ▸ (GeneralizedFitting.normal S.Mbar).conj_mem y hyF _
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h1
      exact mem_zpowers_iff.mpr ⟨i, by simpa using congrArg Subtype.val hi⟩
    obtain ⟨t, htL, ht1, hty⟩ := exists_ne_one_commute_of_four_le hA2 (four_le_card_Lbar H C)
      Nat.prime_three (by norm_num) hyord' hinv
    refine key t htL ht1 (S.Lbar_le_Mbar g htL) ?_
    rw [mem_centralizer_iff]
    intro z hz
    rw [← hzF] at hz
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hz
    have hc : Commute y (⟨t, S.Lbar_le_Mbar g htL⟩ : S.Mbar) := Subtype.ext hty.symm
    exact (hc.zpow_left i).eq

theorem timmesfeld_5_5 (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width) :
    Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧ CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
      timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar := by
  have h3 := card_oddCore_dvd_three H hNo C hn
  refine ⟨h3, (timmesfeld_5_2 hCE hIrr H hNo C Q hn).resolve_left
    (timmesfeldLayer_ne_bot H hNo C hn), ?_⟩
  have hge : timmesfeldOddCore S.Mbar ≤ timmesfeldFitting S.Mbar := by
    refine le_sSup ⟨timmesfeldOddCore_normal _, ?_⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp : IsPGroup 3 (timmesfeldOddCore S.Mbar) := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
    exact hp.isNilpotent
  rw [timmesfeldFStar, le_antisymm (fitting_le_oddCore S) hge]

end CFSG.LargeExtraspecial.S5

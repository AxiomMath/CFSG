module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D5Gas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D5Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D5Iso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D5Mod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D5Model
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem isPGroup2_inf_oddCoreIn_eq_bot {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hP : IsPGroup 2 P) : P ⊓ oddCoreIn K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxP : x ∈ P := hx.1
  have hxO : x ∈ oddCoreIn K := hx.2
  have hodd : Odd (orderOf x) := odd_orderOf_of_mem_oddCoreIn hxO
  obtain ⟨m, hm⟩ := hP.exists_orderOf_dvd_pow ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk] at hm
  have hcop : Nat.Coprime (orderOf x) (2 ^ m) :=
    (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)).symm
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hm)

private theorem mem_normalizer_zpowers_of_commute {G : Type} [Group G] {a x : G}
    (h : x * a = a * x) : x ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (MulAut.conj x a) = Subgroup.zpowers a
  rw [show MulAut.conj x a = a from by rw [MulAut.conj_apply, h]; group]

theorem sec8t84d5_pt (F : Sec8T84Base) {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
    {z g : G} {B E : Subgroup G} (hE : Sec8E G t L S z g B E) :
    ∃ Pt : Subgroup G, Pt ≤ normalizer (E : Set G) ∧ IsPGroup 2 Pt ∧
      (∀ p ∈ Pt, t * p = p * t) ∧ t ∉ Pt ∧ Nat.card ↥Pt = 2 ^ 7 ∧ Sec8T84D5Model Pt := by
  classical
  set N : Subgroup G := Nsub8 t B with hN
  have hset3 : Sec3SettingLB G t L := hE.ctx.toSec3SettingLB
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hset3.involution]
    exact pow_orderOf_eq_one t
  have hLcent : L ≤ centralizer ({t} : Set G) := hset3.component.le
  have hP : IsSylow2Of (S ⊓ L) L :=
    sec4_isSylow2Of_inf hLcent (sec4_mem_normalizer F.h36 hset3)
      hE.ctx.toAsc82Notation.sylow
  have hLM : IsOm6M L := ⟨hset3.component.isQuasisimple, hE.ctx.omega6m⟩
  have hPN : S ⊓ L ≤ N := sec8_SL_le_N F.h36 F.hM hE.ctx
  have hP2 : IsPGroup 2 ↥(S ⊓ L) := hP.2.1
  have hPtc : ∀ p ∈ S ⊓ L, t * p = p * t := by
    intro p hp
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (hE.ctx.toAsc82Notation.sylow.1 hp.1)).symm
  have hEN : E ≤ N := hE.le_N
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 8) hE.elem.2
  have hMnorm : ((E ⊔ oddCoreIn N).subgroupOf N).Normal := hE.normal
  have htN : t ∈ N :=
    Subgroup.le_normalizer (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E := hE.t_norm
  obtain ⟨Pt, hPt_le, hPt2, hPtc', hPt_inf, hPt_sup⟩ :=
    sec8t84d5_lift hEN hE2 hMnorm htN ht2 htE hPN hP2 hPtc
  have hPtN : Pt ≤ N := hPt_le.trans inf_le_left
  have hPtX : Pt ≤ normalizer (E : Set G) := hPt_le.trans inf_le_right
  have hQbot_P : (S ⊓ L) ⊓ oddCoreIn N = ⊥ := isPGroup2_inf_oddCoreIn_eq_bot hP2
  have hnorm : ∀ x ∈ Pt ⊔ oddCoreIn N, ∀ q ∈ oddCoreIn N, x * q * x⁻¹ ∈ oddCoreIn N := by
    intro x hx q hq
    have hxN : x ∈ N := (sup_le hPtN (oddCoreIn_normal N).1) hx
    exact conj_mem_oddCoreIn (Subgroup.le_normalizer hxN) hq
  have hequiv : Nonempty (↥Pt ≃* ↥(S ⊓ L)) :=
    sec8t84d5_equiv_of_sup_eq hPt_inf hQbot_P hPt_sup hnorm
  obtain ⟨hcardPL, hmodelPL⟩ := sec8t84_sylow_model hLM hP
  have hmodelPt : Sec8T84D5Model Pt := sec8t84d5_model_of_equiv hequiv hmodelPL
  have hcardPt : Nat.card ↥Pt = 2 ^ 7 := by
    rw [Nat.card_congr hequiv.some.toEquiv, hcardPL]
  have htPt : t ∉ Pt := by
    intro ht_mem
    have ht_sup : t ∈ (S ⊓ L) ⊔ oddCoreIn N := by
      have h1 : t ∈ Pt ⊔ oddCoreIn N := Subgroup.mem_sup_left ht_mem
      rwa [hPt_sup] at h1
    have hPQ_le_N : (S ⊓ L) ⊔ oddCoreIn N ≤ N :=
      sup_le hPN (oddCoreIn_normal N).1
    haveI hQnormN : ((oddCoreIn N).subgroupOf N).Normal := (oddCoreIn_normal N).2
    have ht' : (⟨t, hPQ_le_N ht_sup⟩ : ↥N) ∈
        (S ⊓ L).subgroupOf N ⊔ (oddCoreIn N).subgroupOf N := by
      rw [← Subgroup.subgroupOf_sup hPN (oddCoreIn_normal N).1]
      exact Subgroup.mem_subgroupOf.mpr ht_sup
    obtain ⟨p', hp', q', hq', hpq'⟩ := Subgroup.mem_sup_of_normal_right.mp ht'
    have hpP : (p' : G) ∈ S ⊓ L := Subgroup.mem_subgroupOf.mp hp'
    have hqQ : (q' : G) ∈ oddCoreIn N := Subgroup.mem_subgroupOf.mp hq'
    have hpq : (p' : G) * (q' : G) = t := by
      have := congrArg (fun z : ↥N => (z : G)) hpq'
      simpa using this
    have hpt : (p' : G) * t = t * (p' : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (hE.ctx.toAsc82Notation.sylow.1 hpP.1)
    have hq_eq : (q' : G) = (p' : G)⁻¹ * t := by
      rw [← hpq]; group
    have hcomm_pq : Commute (p' : G) (q' : G) := by
      show (p' : G) * (q' : G) = (q' : G) * (p' : G)
      rw [hpq, hq_eq, mul_assoc, ← hpt]
      group
    have hsq : (p' : G) ^ 2 * (q' : G) ^ 2 = 1 := by
      have h1 : (p' : G) ^ 2 * (q' : G) ^ 2 = ((p' : G) * (q' : G)) ^ 2 :=
        (hcomm_pq.mul_pow 2).symm
      rw [h1, hpq, pow_two, ht2]
    have hp2_bot : (p' : G) ^ 2 ∈ (S ⊓ L) ⊓ oddCoreIn N := by
      refine ⟨(S ⊓ L).pow_mem hpP 2, ?_⟩
      rw [mul_eq_one_iff_eq_inv.mp hsq]
      exact (oddCoreIn N).inv_mem ((oddCoreIn N).pow_mem hqQ 2)
    have hp2_one : (p' : G) ^ 2 = 1 := by
      have h := hp2_bot
      rw [hQbot_P] at h
      simpa using h
    have hq2_one : (q' : G) ^ 2 = 1 := by
      rw [hp2_one, one_mul] at hsq
      exact hsq
    have hq_one : (q' : G) = 1 := by
      have hodd : Odd (orderOf (q' : G)) := odd_orderOf_of_mem_oddCoreIn hqQ
      have hdvd : orderOf (q' : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hq2_one
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hodd.coprime_two_right hdvd)
    have htP : t ∈ S ⊓ L := by
      rw [← hpq, hq_one, mul_one]
      exact hpP
    have htL : t ∈ L := htP.2
    have hcenter : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro a
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLcent a.2))
    have hmemOdd : (⟨t, htL⟩ : ↥L) ∈ CFSG.oddCore ↥L := by
      rw [← ff_center_eq_oddCore_six_minus hLM]
      exact hcenter
    have hmemOddIn : t ∈ oddCoreIn L := by
      rw [oddCoreIn, CFSG.inSubgroup]
      exact Subgroup.mem_map.mpr ⟨⟨t, htL⟩, hmemOdd, rfl⟩
    have hodd : Odd (orderOf t) := odd_orderOf_of_mem_oddCoreIn hmemOddIn
    rw [hset3.involution] at hodd
    exact (by decide : ¬ Odd 2) hodd
  exact ⟨Pt, hPtX, hPt2, hPtc', htPt, hcardPt, hmodelPt⟩

theorem sec8t84d5_split_one (hMS : Sec8T84ModelSylow) {G : Type} [Group G] [Finite G] {t : G}
    {E Y1 Y2 Pt : Subgroup G} (ht : t * t = 1) (hE : IsElemAb2 E 8)
    (hO : oddCoreIn (normalizer (E : Set G)) ≤ centralizer (E : Set G))
    (hc : Sec8T84XCore G t E Y1 Y2) (hPtX : Pt ≤ normalizer (E : Set G)) (hPt2 : IsPGroup 2 Pt)
    (hPtc : ∀ p ∈ Pt, t * p = p * t) (htPt : t ∉ Pt) (hcard : Nat.card ↥Pt = 2 ^ 7)
    (hmod : Sec8T84D5Model Pt) : Sec8T84SplitFor G E Y1 := by
  classical
  have htX : t ∈ normalizer (E : Set G) := by
    rw [← hc.sup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hzp_le_X : Subgroup.zpowers t ≤ normalizer (E : Set G) :=
    Subgroup.zpowers_le.mpr htX
  have hR_le_X : Pt ⊔ Subgroup.zpowers t ≤ normalizer (E : Set G) := sup_le hPtX hzp_le_X
  have hordvd : orderOf t ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact ht)
  have hzp2 : IsPGroup 2 (Subgroup.zpowers t : Subgroup G) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    simpa [Nat.card_zpowers] using hordvd
  have hPt_norm_zp : Pt ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) :=
    fun p hp => mem_normalizer_zpowers_of_commute (hPtc p hp).symm
  have hR2 : IsPGroup 2 (Pt ⊔ Subgroup.zpowers t : Subgroup G) :=
    hPt2.to_sup_of_normal_right' hzp2 hPt_norm_zp
  obtain ⟨T, hT, hRT⟩ := exists_isSylow2Of_ge hR2 hR_le_X
  have htT : t ∈ T := hRT (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hPtT : Pt ≤ T := le_sup_left.trans hRT
  obtain ⟨_hSylH, _hcardT, _hTsup, hS1, _hS2, _hTinf, _hcomm, _hinf12, _hsw1, _hsw2,
    hET, hEY1, _hEY2, hconjE1, _hconjE2⟩ := sec8t84_tstruct ht hE hc hT htT
  have hcard1 : Nat.card ↥(T ⊓ Y1) = 2 ^ 7 := sec8t84d5_card_sylow hc hS1
  have hiso : Nonempty (↥(T ⊓ Y1) ≃* ↥Pt) :=
    sec8t84d5_iso ht hE hc hT htT hPtT hPtc htPt hcard hcard1
  have hmod1 : Sec8T84D5Model (T ⊓ Y1) := sec8t84d5_model_of_equiv hiso hmod
  have hE1norm : ((E ⊓ Y1).subgroupOf (T ⊓ Y1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEY1).mpr
      (Subgroup.le_normalizer_iff.mpr hconjE1)
  obtain ⟨K, hKle, hKinf, hKsup⟩ :=
    sec8t84d5_complement_of_model hMS hEY1 hc.e16_1 hE1norm hmod1
  obtain ⟨H, hHY, hHinf, hHsup⟩ :=
    sec8t84d5_complement hc hS1 ⟨K, hKle, hKinf, hKsup⟩
  exact sec8t84d5_split_of_complement hO hc hHY hHinf hHsup

theorem sec8t84d5_splitK (F : Sec8T84Base) (hMS : Sec8T84ModelSylow) : Sec8T84SplitK := by
  intro G _ _ _hK t L S z g B E hE Y1 Y2 hc
  obtain ⟨Pt, hPtX, hPt2, hPtc, htPt, hcard, hmod⟩ := sec8t84d5_pt F hE
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hE.ctx.toSec3SettingLB.involution]
    exact pow_orderOf_eq_one t
  have hO : oddCoreIn (normalizer (E : Set G)) ≤ centralizer (E : Set G) :=
    (F.hCE G t L S z g B E hE).2
  exact ⟨sec8t84d5_split_one hMS ht2 hE.elem hO hc hPtX hPt2 hPtc htPt hcard hmod,
    sec8t84d5_split_one hMS ht2 hE.elem hO (sec8t84d5_core_symm hc) hPtX hPt2 hPtc htPt hcard hmod⟩

end CFSG.OddStandard.SmallF3.Omega

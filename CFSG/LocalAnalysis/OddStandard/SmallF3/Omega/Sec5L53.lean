module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Growth

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma53_of (h36 : Asc82Lemma36) (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b)
    (tab : Asc82Tab5) : Asc82Lemma53 := by
  intro G _ _ t L S z h
  have hLN := sec4_mem_normalizer h36 h.toSec3SettingLB
  have hP : IsSylow2Of (S ⊓ L) L := sec4_isSylow2Of_inf h.component.le hLN h.sylow
  have ht2 : orderOf t = 2 := h.involution
  have hz2 : orderOf z = 2 := h.pocket.1
  have hzL : z ∈ L := h.pocket.mem
  have htZ : t ∈ centerIn L := sec5_t_mem_centerIn h52b h.toSec5Setting
  have htS : t ∈ S := sec4_t_mem_S h.sylow ht2
  have ht_centerS : t ∈ centerIn S :=
    sec5_mem_centerIn_iff.mpr ⟨htS, fun s hs =>
      (Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 hs)).symm⟩
  have hz_centerS : z ∈ centerIn S :=
    sec5_mem_centerIn_iff.mpr ⟨h.mem_S, fun s hs => (h.central s hs).symm⟩
  have htz : t * z = z * t := ((sec5_mem_centerIn_iff.mp hz_centerS).2 t htS).symm
  have hzP : z ∈ centerIn (S ⊓ L) :=
    sec5_mem_centerIn_iff.mpr
      ⟨⟨h.mem_S, hzL⟩, fun s hs => (h.central s hs.1).symm⟩
  have ht2' : t ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one t
    rwa [ht2] at hpow
  have hz2' : z ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one z
    rwa [hz2] at hpow
  have hsup_le : zpowers t ⊔ zpowers z ≤ omega1 (centerIn S) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨ht_centerS, ht2'⟩))
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨hz_centerS, hz2'⟩))
  rw [omega1]
  refine le_antisymm ?_ hsup_le
  refine (Subgroup.closure_le (zpowers t ⊔ zpowers z)).mpr ?_
  rintro x ⟨hxcenterS, hx2⟩
  obtain ⟨hxS, hxcommS⟩ := sec5_mem_centerIn_iff.mp hxcenterS
  obtain ⟨hZPeq, hdec⟩ :=
    tab.f53 G L h.toSec5Setting.isOm6Z2 (S ⊓ L) hP t htZ ht2 z h.pocket hzP
  have hxN : x ∈ normalizer (L : Set G) := hLN x (h.sylow.1 hxS)
  obtain ⟨c, hcC, w, hwP, hxw⟩ := hdec x hxN (fun p hp => hxcommS p hp.1)
  have hw : w ∈ zpowers t ⊔ zpowers z := hZPeq ▸ hwP
  have hsupC : zpowers t ⊔ zpowers z ≤ centerIn S :=
    sup_le (Subgroup.zpowers_le.mpr ht_centerS) (Subgroup.zpowers_le.mpr hz_centerS)
  have hwS : w ∈ centerIn S := hsupC hw
  have hc_centerS : c ∈ centerIn S := by
    have hc_eq : c = w⁻¹ * x := by rw [hxw]; group
    rw [hc_eq]
    exact (centerIn S).mul_mem ((centerIn S).inv_mem hwS) hxcenterS
  have hw2 : w * w = 1 := sec5_klein_sq ht2 hz2 htz hw
  have hw2inv : w⁻¹ * w⁻¹ = 1 := by rw [← mul_inv_rev, hw2, inv_one]
  have hx2' : x * x = 1 := by rw [← pow_two]; exact hx2
  have hcomm_xw : x * w = w * x := hxcommS w (sec5_mem_centerIn_iff.mp hwS).1
  have hcomm_xwi : x * w⁻¹ = w⁻¹ * x := by
    calc x * w⁻¹ = w⁻¹ * (w * x) * w⁻¹ := by group
      _ = w⁻¹ * (x * w) * w⁻¹ := by rw [hcomm_xw]
      _ = w⁻¹ * x := by group
  have hc2 : c * c = 1 := by
    have hc_eq : c = w⁻¹ * x := by rw [hxw]; group
    rw [hc_eq]
    calc (w⁻¹ * x) * (w⁻¹ * x) = w⁻¹ * (x * w⁻¹) * x := by group
      _ = w⁻¹ * (w⁻¹ * x) * x := by rw [hcomm_xwi]
      _ = (w⁻¹ * w⁻¹) * (x * x) := by group
      _ = 1 := by rw [hw2inv, hx2', mul_one]
  have hct : c * t = t * c := (sec5_mem_centerIn_iff.mp hc_centerS).2 t htS
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer h.toSec3Setting
  have hcyc : ∀ P : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (P : Subgroup (centralizer (L : Set G))) := h52a G t L h.toSec5Setting
  rcases sec4_eq_of_commute hcyc hcC htC hc2 ht2 hct with hc1 | hct_eq
  · rw [hxw, hc1, mul_one]
    exact hw
  · rw [hxw, hct_eq]
    exact (zpowers t ⊔ zpowers z).mul_mem hw (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))

end CFSG.OddStandard.SmallF3.Omega

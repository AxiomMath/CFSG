module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMARCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.ExtraspecialCriterion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

private lemma coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

private theorem add_self_eq_zero_V6 (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

theorem Rgrp_center_le (h : Setting25 G t z z₁ ι zv R0 F) {x : G} (hx : x ∈ Rgrp h)
    (hc : ∀ y ∈ Rgrp h, x * y = y * x) : x ∈ zpowers z := by
  obtain ⟨u, hE⟩ := Rgrp_eichActs h hx
  have key : ∀ v : V6, bil v zv = 0 → bil v u = 0 := by
    intro v hv
    have hcv : coordElt ι v ∈ Cgrp ι zv := (coordElt_mem_Cgrp h.injective_ι).2 hv
    have hcvR : coordElt ι v ∈ Rgrp h := Cgrp_le_Rgrp h hcv
    have hcomm : x * coordElt ι v = coordElt ι v * x := hc _ hcvR
    have hconj : x * coordElt ι v * x⁻¹ = coordElt ι v := by
      rw [hcomm]; group
    rw [hE.2 v] at hconj
    have heich : eichF zv u v = v := coordElt_injective h.injective_ι hconj
    have h0 : eichF zv u v + v = 0 := by rw [heich, add_self_eq_zero_V6]
    rw [eichF_add_self] at h0
    rw [hv] at h0
    simp only [zero_smul, mul_zero, add_zero, zero_add] at h0
    rcases eq_zero_or_eq_zero_of_smul_eq_zero h0 with hb | hz
    · exact hb
    · exact absurd hz h.zv_ne_zero
  have hu01 : u = 0 ∨ u = zv :=
    eq_zero_or_eq_of_perp_perp h.hD2.qm_zv h.zv_ne_zero hE.1
      (fun u' hu' => by rw [bil_comm]; exact key u' hu')
  have hxrange : x ∈ ι.range :=
    EichActs.mem_range_of_eq_zero_or_eq h.centralizer_le h.hD2.qm_zv hE hu01
  have hxC : x ∈ Cgrp ι zv := by
    rw [← Rgrp_inf_range h]
    exact ⟨hx, hxrange⟩
  obtain ⟨a, ha_perp, ha_eq⟩ := mem_Cgrp.mp hxC
  have key2 : ∀ u' : V6, bil u' zv = 0 → bil a u' = 0 := by
    intro u' hu'
    obtain ⟨y, hyR, hyE⟩ := exists_mem_Rgrp h hu'
    have hyx : y⁻¹ * x * y = x := by
      have hcy := hc y hyR
      rw [mul_assoc, hcy]
      group
    have hstep : y⁻¹ * coordElt ι a * y = coordElt ι a := by
      rw [ha_eq]
      exact hyx
    have hstep2 : coordElt ι (eichF zv u' a) = coordElt ι a := by
      rw [← hyE.inv.2 a, inv_inv]
      exact hstep
    have heich : eichF zv u' a = a := coordElt_injective h.injective_ι hstep2
    have h0 : eichF zv u' a + a = 0 := by rw [heich, add_self_eq_zero_V6]
    rw [eichF_add_self] at h0
    rw [ha_perp] at h0
    simp only [zero_smul, mul_zero, add_zero, zero_add] at h0
    rcases eq_zero_or_eq_zero_of_smul_eq_zero h0 with hb | hz
    · exact hb
    · exact absurd hz h.zv_ne_zero
  have ha01 : a = 0 ∨ a = zv :=
    eq_zero_or_eq_of_perp_perp h.hD2.qm_zv h.zv_ne_zero ha_perp key2
  rcases ha01 with ha0 | haz
  · rw [← ha_eq, ha0, coordElt_zero]
    exact one_mem _
  · rw [← ha_eq, haz, h.coord_z]
    exact Subgroup.mem_zpowers z

theorem center_Rgrp_eq (h : Setting25 G t z z₁ ι zv R0 F) :
    center ↥(Rgrp h) = (zpowers z).subgroupOf (Rgrp h) := by
  ext x
  rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    exact Rgrp_center_le h x.2 (fun y hy => (Subtype.ext_iff.mp (hx ⟨y, hy⟩)).symm)
  · intro hx g
    apply Subtype.ext
    have hgK : (g : G) ∈ Kgrp ι z := Rgrp_le_K h g.2
    have hgz : Commute (g : G) z :=
      Subgroup.mem_centralizer_singleton_iff.mp hgK.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    show (g : G) * (x : G) = (x : G) * (g : G)
    rw [← hm]
    exact hgz.zpow_right m

theorem card_center_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) :
    Nat.card (center ↥(Rgrp h)) = 2 := by
  have hle : zpowers z ≤ Rgrp h := Subgroup.zpowers_le.mpr (z_mem_Rgrp h)
  rw [center_Rgrp_eq h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  haveI : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_zpowers]
  exact orderOf_eq_prime h.z_sq h.z_ne_one

theorem isExtraspecial_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) :
    CFSG.IsExtraspecial 2 ↥(Rgrp h) := by
  refine isExtraspecial_two_of_sq_comm_mem_center (P := ↥(Rgrp h))
    (card_center_Rgrp h) ?_ ?_ ?_
  · intro x
    rw [center_Rgrp_eq h, Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_pow] using Rgrp_sq h x.2
  · intro x y
    rw [center_Rgrp_eq h, Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using Rgrp_comm h x.2 y.2
  · by_contra hnt
    push_neg at hnt
    have htop : center ↥(Rgrp h) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact hnt x
    have h2 : Nat.card (center ↥(Rgrp h)) = 2 ^ 9 := by
      rw [htop, Subgroup.card_top, card_Rgrp h]
    rw [card_center_Rgrp h] at h2
    norm_num at h2

theorem isPlusExtraspecial_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) :
    IsPlusExtraspecial 4 (Rgrp h) := by
  refine ⟨isExtraspecial_Rgrp h, ?_, Cgrp ι zv, Cgrp_le_Rgrp h, ?_, ?_⟩
  · norm_num [card_Rgrp h]
  · refine ⟨isMulCommutative_iff.mpr (fun a b => Subtype.ext (Cgrp_mul_comm a.2 b.2)), ?_⟩
    intro x hx
    simpa using Cgrp_sq hx
  · norm_num [card_Cgrp h.injective_ι h.zv_ne_zero]

end CFSG.EvenSporadicStandard.HNRecog.Harada

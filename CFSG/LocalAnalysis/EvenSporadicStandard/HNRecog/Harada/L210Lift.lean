module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Inputs

public section

open scoped commutatorElement

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)

private lemma zpowers_subgroupOf_Mgrp_le_center (z : G) :
    (zpowers z).subgroupOf (Mgrp z) ≤ Subgroup.center ↥(Mgrp z) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro m
  apply Subtype.ext
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
  have hm : Commute (m : G) z := Subgroup.mem_centralizer_singleton_iff.mp m.2
  simp only [Subgroup.coe_mul]
  rw [← hk]
  exact (hm.zpow_right k).eq

private lemma commutator_mul_central {H : Type*} [Group H] {z₁ z₂ y₁ y₂ : H}
    (h₁ : z₁ ∈ Subgroup.center H) (h₂ : z₂ ∈ Subgroup.center H) :
    ⁅y₁ * z₁, y₂ * z₂⁆ = ⁅y₁, y₂⁆ := by
  have hz₁ : ⁅z₁, y₂ * z₂⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr ((Subgroup.mem_center_iff.mp h₁ (y₂ * z₂)).symm)
  have hz₂ : ⁅y₁, z₂⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp h₂ y₁)
  rw [commutatorElement_mul_left_eq_conj_mul, hz₁]
  rw [commutatorElement_mul_right_eq_mul_conj, hz₂]
  group

private lemma commutator_mul_central_target {H : Type*} [Group H] {Z : Subgroup H}
    (hZ : Z ≤ Subgroup.center H) {t a b : H}
    (ha : ⁅a, t⁆ ∈ Z) (hb : ⁅b, t⁆ ∈ Z) :
    ⁅a * b, t⁆ = ⁅a, t⁆ * ⁅b, t⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hb_comm : Commute a ⁅b, t⁆ := Subgroup.mem_center_iff.mp (hZ hb) a
  rw [hb_comm.eq]
  have hsimp : (⁅b, t⁆ * a) * a⁻¹ * ⁅a, t⁆ = ⁅b, t⁆ * ⁅a, t⁆ := by group
  rw [hsimp]
  exact Subgroup.mem_center_iff.mp (hZ ha) ⁅b, t⁆

private theorem central_extension_perfect
    {H Q : Type*} [Group H] [Group Q]
    (Z : Subgroup H) (hZ : Z ≤ Subgroup.center H)
    (π : H →* Q) (hπ : Function.Surjective π) (hker : π.ker = Z)
    (t : H) (D : Subgroup Q) (hDcent : ∀ d ∈ D, d * π t = π t * d)
    (hDperf : ⁅D, D⁆ = D) :
    ⁅D.comap π, D.comap π⁆ ≤ Subgroup.centralizer ({t} : Set H) ∧
      ⁅⁅D.comap π, D.comap π⁆, ⁅D.comap π, D.comap π⁆⁆ = ⁅D.comap π, D.comap π⁆ := by
  set Dt : Subgroup H := D.comap π with hDt
  set Y0 : Subgroup H := ⁅Dt, Dt⁆ with hY0
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  have hmem_c : ∀ y : ↥Dt, ⁅(y : H), t⁆ ∈ Z := by
    intro y
    rw [commutatorElement_def, ← hker, MonoidHom.mem_ker]
    have hcomm : π (y : H) * π t = π t * π (y : H) := hDcent (π (y : H)) y.2
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  let c : ↥Dt →* ↥Z :=
    MonoidHom.mk' (fun y => ⟨⁅(y : H), t⁆, hmem_c y⟩) (by
      intro y y'
      apply Subtype.ext
      change ⁅(y : H) * (y' : H), t⁆ = ⁅(y : H), t⁆ * ⁅(y' : H), t⁆
      exact commutator_mul_central_target hZ (hmem_c y) (hmem_c y'))
  have hc_one : ∀ x : ↥Dt, c x = 1 → (x : H) * t = t * (x : H) := by
    intro x hx
    have hx' : ⁅(x : H), t⁆ = 1 := by
      change ((c x : ↥Z) : H) = 1
      rw [hx]
      rfl
    exact commutatorElement_eq_one_iff_commute.mp hx'
  have hY0_cent : ⁅Dt, Dt⁆ ≤ Subgroup.centralizer ({t} : Set H) := by
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine hc_one ⟨⁅a, b⁆, Subgroup.commutator_le_self Dt
      (Subgroup.commutator_mem_commutator ha hb)⟩ ?_
    have hmap := map_commutatorElement c (⟨a, ha⟩ : ↥Dt) (⟨b, hb⟩ : ↥Dt)
    have hcoe : (⟨⁅a, b⁆, Subgroup.commutator_le_self Dt
        (Subgroup.commutator_mem_commutator ha hb)⟩ : ↥Dt) =
        ⁅(⟨a, ha⟩ : ↥Dt), (⟨b, hb⟩ : ↥Dt)⁆ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [hcoe, hmap]
    exact commutatorElement_eq_one_iff_commute.mpr
      (Subtype.ext (Subgroup.mem_center_iff.mp (hZ (c ⟨b, hb⟩).2) (c ⟨a, ha⟩ : H)))
  have hπDt : Dt.map π = D := Subgroup.map_comap_eq_self_of_surjective hπ D
  have hπY0 : Y0.map π = D := by
    rw [hY0, Subgroup.map_commutator, hπDt, hDperf]
  have hDt_le : Dt ≤ Y0 ⊔ Z := by
    intro y hy
    have hyD : π y ∈ Y0.map π := by rw [hπY0]; exact hy
    obtain ⟨y0, hy0, hy0eq⟩ := Subgroup.mem_map.mp hyD
    have hz : y * y0⁻¹ ∈ Z := by
      rw [← hker, MonoidHom.mem_ker]
      rw [map_mul, map_inv, hy0eq, mul_inv_cancel]
    rw [Subgroup.mem_sup_of_normal_right]
    refine ⟨y0, hy0, y * y0⁻¹, hz, ?_⟩
    rw [Subgroup.mem_center_iff.mp (hZ hz) y0]
    group
  have hY0_le : Y0 ≤ ⁅Y0, Y0⁆ := by
    rw [hY0]
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hDt_le ha)
    obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hDt_le hb)
    rw [commutator_mul_central (hZ ha2) (hZ hb2)]
    exact Subgroup.commutator_mem_commutator ha1 hb1
  have hY0_perf : ⁅Y0, Y0⁆ = Y0 := le_antisymm (Subgroup.commutator_le_self Y0) hY0_le
  exact ⟨hY0_cent, hY0_perf⟩

theorem noA5_Aq (hF : Facts210 G t z) :
    ∀ D : Subgroup (Xq z), D ≤ normalizer (Aq h : Set (Xq z)) →
      (∀ d ∈ D, d * wq h = wq h * d) → IsEmpty (↥D ≃* alternatingGroup (Fin 5)) := by
  intro D _hDnorm hDcent
  refine ⟨fun e => ?_⟩
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  haveI : Group.IsPerfect ↥D :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) (MulEquiv.surjective e.symm)
  have hDperf : ⁅D, D⁆ = D := Subgroup.commutator_eq_self
  let Z : Subgroup ↥(Mgrp z) := (zpowers z).subgroupOf (Mgrp z)
  have hZ : Z ≤ Subgroup.center ↥(Mgrp z) := zpowers_subgroupOf_Mgrp_le_center z
  let t' : ↥(Mgrp z) := ⟨t, t_mem_Mgrp h⟩
  have hDcent' : ∀ d ∈ D, d * piq z t' = piq z t' * d := fun d hd => hDcent d hd
  have hmain := central_extension_perfect Z hZ (piq z) (piq_surjective z) (ker_piq z)
    t' D hDcent' hDperf
  set Y0 : Subgroup ↥(Mgrp z) := ⁅D.comap (piq z), D.comap (piq z)⁆ with hY0def
  have hY0_cent : Y0 ≤ Subgroup.centralizer ({t'} : Set ↥(Mgrp z)) := by
    rw [hY0def]; exact hmain.1
  have hY0_perf : ⁅Y0, Y0⁆ = Y0 := by
    rw [hY0def]; exact hmain.2
  have hY0_le_Dt : Y0 ≤ D.comap (piq z) := by
    rw [hY0def]; exact Subgroup.commutator_le_self _
  let Y : Subgroup G := Y0.map (Mgrp z).subtype
  have hY_le_M : Y ≤ Mgrp z := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp (show y ∈ Y0.map (Mgrp z).subtype from hy)
    exact m.2
  have hY_le : Y ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp (show y ∈ Y0.map (Mgrp z).subtype from hy)
    rw [Subgroup.mem_inf]
    constructor
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hmt : m * t' = t' * m := Subgroup.mem_centralizer_singleton_iff.mp (hY0_cent hm)
      have hc := congrArg (fun x : ↥(Mgrp z) => (x : G)) hmt
      simpa [t'] using hc
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_singleton_iff.mp m.2
  have hY_perf : ⁅Y, Y⁆ = Y := by
    show ⁅Y0.map (Mgrp z).subtype, Y0.map (Mgrp z).subtype⁆ = Y0.map (Mgrp z).subtype
    rw [← Subgroup.map_commutator, hY0_perf]
  let g : ↥Y →* ↥(Mgrp z) := Subgroup.inclusion hY_le_M
  have hmem_f : ∀ y : ↥Y, piq z (g y) ∈ D := by
    intro y
    obtain ⟨m, hm, hmy⟩ :=
      Subgroup.mem_map.mp (show (y : G) ∈ Y0.map (Mgrp z).subtype from y.2)
    have hmD : m ∈ D.comap (piq z) := hY0_le_Dt hm
    have hpi : piq z (g y) = piq z m := by
      apply congrArg (piq z)
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
      exact hmy.symm
    rw [hpi]
    exact hmD
  let f : ↥Y →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (MonoidHom.codRestrict ((piq z).comp g) D hmem_f)
  have hπY0 : Y0.map (piq z) = D := by
    rw [hY0def, Subgroup.map_commutator]
    rw [Subgroup.map_comap_eq_self_of_surjective (piq_surjective z) D, hDperf]
  have hf_surj : Function.Surjective f := by
    intro a
    have haD : (e.symm a : Xq z) ∈ Y0.map (piq z) := by rw [hπY0]; exact (e.symm a).2
    obtain ⟨y0, hy0, hy0eq⟩ := Subgroup.mem_map.mp haD
    let yw : ↥Y := ⟨(y0 : G), Subgroup.mem_map_of_mem (Mgrp z).subtype hy0⟩
    refine ⟨yw, ?_⟩
    have hgy : g yw = y0 := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
    show e ((MonoidHom.codRestrict ((piq z).comp g) D hmem_f) yw) = a
    have hval : (MonoidHom.codRestrict ((piq z).comp g) D hmem_f) yw = e.symm a := by
      apply Subtype.ext
      rw [MonoidHom.codRestrict_apply]
      show piq z (g yw) = (e.symm a : Xq z)
      rw [hgy, hy0eq]
    rw [hval]
    exact e.apply_symm_apply a
  have hf_ker : f.ker ≤ (zpowers z).subgroupOf Y := by
    intro y hy
    have hfy : e ((MonoidHom.codRestrict ((piq z).comp g) D hmem_f) y) = 1 := hy
    have hcr1 : ((MonoidHom.codRestrict ((piq z).comp g) D hmem_f) y : Xq z) = 1 := by
      simpa using congrArg e.symm hfy
    have hpi1 : piq z (g y) = 1 := by
      simpa [MonoidHom.codRestrict_apply] using hcr1
    have hgZ : (g y : ↥(Mgrp z)) ∈ Z := by
      change (g y : ↥(Mgrp z)) ∈ (zpowers z).subgroupOf (Mgrp z)
      rw [← ker_piq z, MonoidHom.mem_ker]
      exact hpi1
    rw [Subgroup.mem_subgroupOf]
    have hgz : ((g y : ↥(Mgrp z)) : G) ∈ zpowers z := Subgroup.mem_subgroupOf.mp hgZ
    rw [Subgroup.coe_inclusion] at hgz
    exact hgz
  exact hF Y hY_le hY_perf f hf_surj hf_ker

end CFSG.EvenSporadicStandard.HNRecog.Harada

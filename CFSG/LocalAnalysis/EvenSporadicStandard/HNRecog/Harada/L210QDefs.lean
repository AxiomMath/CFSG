module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NRCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NRStab

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

abbrev Mgrp (z : G) : Subgroup G := centralizer ({z} : Set G)

instance normal_zpowers_subgroupOf_Mgrp (z : G) : ((zpowers z).subgroupOf (Mgrp z)).Normal :=
  Subgroup.normal_of_le_center (by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
    have hm : Commute (m : G) z := Subgroup.mem_centralizer_singleton_iff.mp m.2
    simp only [Subgroup.coe_mul]
    rw [← hk]
    exact (hm.zpow_right k).eq)

abbrev Xq (z : G) : Type := ↥(Mgrp z) ⧸ (zpowers z).subgroupOf (Mgrp z)

@[expose] def piq (z : G) : ↥(Mgrp z) →* Xq z := QuotientGroup.mk' _

theorem Rgrp_le_Mgrp (h : Setting25 G t z z₁ ι zv R0 F) : Rgrp h ≤ Mgrp z := by
  intro x hx
  have hK := Rgrp_le_K h hx
  rw [Kgrp] at hK
  exact (Subgroup.mem_inf.mp hK).2

theorem normalizer_Rgrp_le_Mgrp (h : Setting25 G t z z₁ ι zv R0 F) :
    normalizer (Rgrp h : Set G) ≤ Mgrp z := by
  intro n hn
  rw [Mgrp, Subgroup.mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul.mp (conj_z_of_mem_normalizer_Rgrp h hn)

theorem t_mem_Mgrp (h : Setting25 G t z z₁ ι zv R0 F) : t ∈ Mgrp z :=
  Rgrp_le_Mgrp h (Setting25.t_mem_Rgrp h)

@[expose] def Aq (h : Setting25 G t z z₁ ι zv R0 F) : Subgroup (Xq z) :=
  ((Rgrp h).subgroupOf (Mgrp z)).map (piq z)

@[expose] def wq (h : Setting25 G t z z₁ ι zv R0 F) : Xq z := piq z ⟨t, t_mem_Mgrp h⟩

theorem piq_surjective (z : G) : Function.Surjective (piq z) :=
  QuotientGroup.mk'_surjective ((zpowers z).subgroupOf (Mgrp z))

theorem ker_piq (z : G) : (piq z).ker = (zpowers z).subgroupOf (Mgrp z) :=
  QuotientGroup.ker_mk' ((zpowers z).subgroupOf (Mgrp z))

theorem mem_Aq_iff (h : Setting25 G t z z₁ ι zv R0 F) (m : ↥(Mgrp z)) :
    piq z m ∈ Aq h ↔ (m : G) ∈ Rgrp h := by
  constructor
  · intro hm
    rw [Aq] at hm
    obtain ⟨x, hx, hxm⟩ := Subgroup.mem_map.mp hm
    have hxR : (x : G) ∈ Rgrp h := Subgroup.mem_subgroupOf.mp hx
    have hxm' : (x : Xq z) = (m : Xq z) := hxm
    have hker : x⁻¹ * m ∈ (zpowers z).subgroupOf (Mgrp z) :=
      (QuotientGroup.eq (s := (zpowers z).subgroupOf (Mgrp z))).mp hxm'
    have hzR : ((x⁻¹ * m : ↥(Mgrp z)) : G) ∈ Rgrp h :=
      Subgroup.zpowers_le.mpr (z_mem_Rgrp h) (Subgroup.mem_subgroupOf.mp hker)
    have hm_eq : (m : G) = (x : G) * ((x⁻¹ * m : ↥(Mgrp z)) : G) := by
      rw [← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [hm_eq]
    exact mul_mem hxR hzR
  · intro hm
    rw [Aq]
    exact Subgroup.mem_map_of_mem (piq z) (Subgroup.mem_subgroupOf.mpr hm)

private lemma piq_conj_eq (m m' : ↥(Mgrp z)) :
    piq z (m * m' * m⁻¹) = piq z m * piq z m' * (piq z m)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem mem_normalizer_Aq_iff (h : Setting25 G t z z₁ ι zv R0 F) (m : ↥(Mgrp z)) :
    piq z m ∈ normalizer (Aq h : Set (Xq z)) ↔ (m : G) ∈ normalizer (Rgrp h : Set G) := by
  constructor
  · intro hm
    rw [Subgroup.mem_set_normalizer_iff] at hm
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyM : y ∈ Mgrp z := Rgrp_le_Mgrp h hy
      have hmem : piq z ⟨y, hyM⟩ ∈ Aq h := (mem_Aq_iff h ⟨y, hyM⟩).mpr hy
      have hconj : piq z m * piq z ⟨y, hyM⟩ * (piq z m)⁻¹ ∈ Aq h :=
        (hm (piq z ⟨y, hyM⟩)).mp hmem
      have hconj' : piq z (m * ⟨y, hyM⟩ * m⁻¹) ∈ Aq h := by
        rw [piq_conj_eq m ⟨y, hyM⟩]
        exact hconj
      have hR : ((m * ⟨y, hyM⟩ * m⁻¹ : ↥(Mgrp z)) : G) ∈ Rgrp h :=
        (mem_Aq_iff h (m * ⟨y, hyM⟩ * m⁻¹)).mp hconj'
      simpa [Subgroup.coe_mul] using hR
    · intro hy
      have hyM : y ∈ Mgrp z := by
        have h1 : (m : G)⁻¹ * ((m : G) * y * (m : G)⁻¹) * (m : G) ∈ Mgrp z :=
          mul_mem (mul_mem (inv_mem m.2) (Rgrp_le_Mgrp h hy)) m.2
        have h2 : (m : G)⁻¹ * ((m : G) * y * (m : G)⁻¹) * (m : G) = y := by group
        rwa [h2] at h1
      have hconjAq : piq z m * piq z ⟨y, hyM⟩ * (piq z m)⁻¹ ∈ Aq h := by
        rw [← piq_conj_eq m ⟨y, hyM⟩]
        exact (mem_Aq_iff h (m * ⟨y, hyM⟩ * m⁻¹)).mpr (by
          simpa [Subgroup.coe_mul] using hy)
      exact (mem_Aq_iff h ⟨y, hyM⟩).mp ((hm (piq z ⟨y, hyM⟩)).mpr hconjAq)
  · intro hm
    rw [Subgroup.mem_set_normalizer_iff] at hm
    rw [Subgroup.mem_set_normalizer_iff]
    intro w
    obtain ⟨m', rfl⟩ := piq_surjective z w
    show piq z m' ∈ Aq h ↔ piq z m * piq z m' * (piq z m)⁻¹ ∈ Aq h
    rw [mem_Aq_iff h m', ← piq_conj_eq m m', mem_Aq_iff h (m * m' * m⁻¹)]
    have hcoe : ((m * m' * m⁻¹ : ↥(Mgrp z)) : G) = (m : G) * (m' : G) * (m : G)⁻¹ := by
      simp [Subgroup.coe_mul]
    rw [hcoe]
    exact hm (m' : G)

theorem wq_mem_Aq (h : Setting25 G t z z₁ ι zv R0 F) : wq h ∈ Aq h := by
  rw [wq]
  exact (mem_Aq_iff h ⟨t, t_mem_Mgrp h⟩).mpr (Setting25.t_mem_Rgrp h)

@[expose] def piN (h : Setting25 G t z z₁ ι zv R0 F) :
    ↥(normalizer (Rgrp h : Set G)) →* ↥(normalizer (Aq h : Set (Xq z))) :=
  MonoidHom.codRestrict ((piq z).comp (Subgroup.inclusion (normalizer_Rgrp_le_Mgrp h)))
    (normalizer (Aq h : Set (Xq z)))
    (fun n => (mem_normalizer_Aq_iff h ⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩).2 n.2)

theorem piN_val (h : Setting25 G t z z₁ ι zv R0 F) (n : ↥(normalizer (Rgrp h : Set G))) :
    ((piN h n : ↥(normalizer (Aq h : Set (Xq z)))) : Xq z) =
      piq z ⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩ := rfl

theorem piN_surjective (h : Setting25 G t z z₁ ι zv R0 F) : Function.Surjective (piN h) := by
  intro x
  obtain ⟨m, hm⟩ := piq_surjective z (x : Xq z)
  have hmAq : piq z m ∈ normalizer (Aq h : Set (Xq z)) := by
    rw [hm]
    exact x.2
  have hmN : (m : G) ∈ normalizer (Rgrp h : Set G) := (mem_normalizer_Aq_iff h m).mp hmAq
  refine ⟨⟨(m : G), hmN⟩, ?_⟩
  apply Subtype.ext
  rw [piN_val]
  rw [show (⟨(m : G), normalizer_Rgrp_le_Mgrp h hmN⟩ : ↥(Mgrp z)) = m from Subtype.ext rfl]
  exact hm

theorem ker_piN (h : Setting25 G t z z₁ ι zv R0 F) :
    (piN h).ker = (zpowers z).subgroupOf (normalizer (Rgrp h : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hn
    have hval : piq z ⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩ = 1 := by
      have h1 := congrArg (fun y : ↥(normalizer (Aq h : Set (Xq z))) => (y : Xq z)) hn
      simpa [piN_val] using h1
    have hker : (⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩ : ↥(Mgrp z)) ∈ (piq z).ker :=
      MonoidHom.mem_ker.mpr hval
    rw [ker_piq z] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  · intro hn
    have hker : (⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩ : ↥(Mgrp z)) ∈ (piq z).ker := by
      rw [ker_piq z]
      exact Subgroup.mem_subgroupOf.mpr hn
    have hval : piq z ⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩ = 1 :=
      MonoidHom.mem_ker.mp hker
    apply Subtype.ext
    rw [piN_val]
    simpa using hval

end CFSG.EvenSporadicStandard.HNRecog.Harada

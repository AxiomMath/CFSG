module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)
  {φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo}

theorem wq_ne_one (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) : wq h ≠ 1 := by
  intro hw
  have ht : t ∈ zpowers z := by
    have hmem : (⟨t, t_mem_Mgrp h⟩ : ↥(Mgrp z)) ∈ (zpowers z).subgroupOf (Mgrp z) := by
      rw [← ker_piq z, MonoidHom.mem_ker]
      simpa only [wq] using hw
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hord : orderOf z = 2 := orderOf_eq_prime h.z_sq h.z_ne_one
  rw [← zpow_mod_orderOf z k, hord] at hk
  norm_num only [Nat.cast_ofNat] at hk
  rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
  ·
    rw [hk2] at hk
    simp only [zpow_zero] at hk
    have ht1 : t = 1 := hk.symm
    have hconj : IsConj (1 : G) z := by
      have h' := htz
      rw [ht1, one_mul] at h'
      exact h'
    exact h.z_ne_one (isConj_one_right.mp hconj)
  ·
    rw [hk2] at hk
    simp only [zpow_one] at hk
    exact hzt (by rw [← hk])

theorem faithful_Aq (hs : Lemma27Spec h φ) :
    ∀ x ∈ normalizer (Aq h : Set (Xq z)), (∀ a ∈ Aq h, x * a = a * x) → x ∈ Aq h := by
  intro x hx hcomm
  obtain ⟨m, hm⟩ := piq_surjective z x
  have hx' : piq z m ∈ normalizer (Aq h : Set (Xq z)) := by rwa [hm]
  have hmg : (m : G) ∈ normalizer (Rgrp h : Set G) :=
    (mem_normalizer_Aq_iff h m).1 hx'
  have hker : ∀ r ∈ Rgrp h, (m : G) * r * (m : G)⁻¹ * r⁻¹ ∈ zpowers z := by
    intro r hr
    have hrm : r ∈ Mgrp z := Rgrp_le_Mgrp h hr
    have hr'mem : piq z (⟨r, hrm⟩ : ↥(Mgrp z)) ∈ Aq h := by
      rw [Aq]
      exact Subgroup.mem_map_of_mem (piq z) (Subgroup.mem_subgroupOf.mpr hr)
    have hcomm' : piq z m * piq z (⟨r, hrm⟩ : ↥(Mgrp z)) =
        piq z (⟨r, hrm⟩ : ↥(Mgrp z)) * piq z m := by
      have h' := hcomm (piq z (⟨r, hrm⟩ : ↥(Mgrp z))) hr'mem
      rwa [← hm] at h'
    have h1 : piq z (m * (⟨r, hrm⟩ : ↥(Mgrp z)) * m⁻¹ * (⟨r, hrm⟩ : ↥(Mgrp z))⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm']
      group
    have h2 : (m * (⟨r, hrm⟩ : ↥(Mgrp z)) * m⁻¹ * (⟨r, hrm⟩ : ↥(Mgrp z))⁻¹) ∈
        (piq z).ker := MonoidHom.mem_ker.mpr h1
    rw [ker_piq z] at h2
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa using h3
  have hmR : (m : G) ∈ Rgrp h := hs.faithful (m : G) hmg hker
  rw [← hm]
  exact (mem_Aq_iff h m).2 hmR

end CFSG.EvenSporadicStandard.HNRecog.Harada

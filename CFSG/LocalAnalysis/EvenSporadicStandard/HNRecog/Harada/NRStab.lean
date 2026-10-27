module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NVR
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAExtra

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

theorem conj_z_of_mem_normalizer_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) {n : G}
    (hn : n ∈ normalizer (Rgrp h : Set G)) : n * z * n⁻¹ = z := by
  have hwR : n * z * n⁻¹ ∈ Rgrp h :=
    (Subgroup.mem_set_normalizer_iff.mp hn z).mp (z_mem_Rgrp h)
  have hcomm : ∀ y ∈ Rgrp h, (n * z * n⁻¹) * y = y * (n * z * n⁻¹) := by
    intro y hy
    have hny : n⁻¹ * y * n ∈ Rgrp h :=
      (Subgroup.mem_set_normalizer_iff''.mp hn y).mp hy
    have hzy : z * (n⁻¹ * y * n) = (n⁻¹ * y * n) * z :=
      (Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (Rgrp_le_K h hny)).2).symm
    calc (n * z * n⁻¹) * y
        = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by rw [hzy]
      _ = y * (n * z * n⁻¹) := by group
  have hwzp : n * z * n⁻¹ ∈ zpowers z := Rgrp_center_le h hwR hcomm
  have hw_ne_one : n * z * n⁻¹ ≠ 1 := by
    intro h1
    apply h.z_ne_one
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  rcases Subgroup.mem_zpowers_iff.mp hwzp with ⟨k, hk⟩
  have hord : orderOf z = 2 := orderOf_eq_prime h.z_sq h.z_ne_one
  rw [← zpow_mod_orderOf z k, hord] at hk
  norm_num only [Nat.cast_ofNat] at hk
  rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
  · rw [hk2] at hk
    simp at hk
    exact absurd hk.symm hw_ne_one
  · rw [hk2] at hk
    simpa only [zpow_one] using hk.symm

theorem mem_normalizer_V_iff_mem_normalizer_Rgrp (h : Setting25 G t z z₁ ι zv R0 F)
    (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) {n : G} :
    n ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) ↔
      n ∈ normalizer (Rgrp h : Set G) ∧ (n * t * n⁻¹ = t ∨ n * t * n⁻¹ = t * z) := by
  constructor
  · intro hn
    refine ⟨?_, conj_t_of_mem_normalizer_V h.t_sq h.z_sq h.t_mul_z_comm hzt htz hn⟩
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact Rgrp_conj_of_mem_normalizer_V h hzt htz hn hy
    · intro hy
      have h' := Rgrp_conj_of_mem_normalizer_V h hzt htz (inv_mem hn) hy
      rwa [show n⁻¹ * (n * y * n⁻¹) * (n⁻¹)⁻¹ = y from by group] at h'
  · rintro ⟨hnR, hnt⟩
    exact mem_normalizer_V_of_conj h.t_sq h.z_sq h.t_mul_z_comm
      (conj_z_of_mem_normalizer_Rgrp h hnR) hnt

end CFSG.EvenSporadicStandard.HNRecog.Harada

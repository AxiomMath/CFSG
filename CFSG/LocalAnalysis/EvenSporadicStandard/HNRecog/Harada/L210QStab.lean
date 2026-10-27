module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QHom

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)
  {φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo}

private theorem piN_mem_centralizer_iff (hzt : ¬ IsConj t z) (htz : IsConj t (t * z))
    (n : ↥(normalizer (Rgrp h : Set G))) :
    piN h n ∈ centralizer
      ({(⟨wq h, Subgroup.le_normalizer (wq_mem_Aq h)⟩ :
        ↥(normalizer (Aq h : Set (Xq z))))} :
        Set ↥(normalizer (Aq h : Set (Xq z)))) ↔
      (n : G) ∈ NVgrp t z := by
  set w' : ↥(normalizer (Aq h : Set (Xq z))) :=
    ⟨wq h, Subgroup.le_normalizer (wq_mem_Aq h)⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hval : piN h n * w' = w' * piN h n ↔
      (piN h n : Xq z) * wq h = wq h * (piN h n : Xq z) := by
    constructor
    · intro hh; exact congrArg Subtype.val hh
    · intro hh; exact Subtype.ext hh
  rw [hval]
  simp only [piN_val, wq]
  set nm : ↥(Mgrp z) := ⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩ with hnm
  set tm : ↥(Mgrp z) := ⟨t, t_mem_Mgrp h⟩ with htm
  have hker : piq z nm * piq z tm = piq z tm * piq z nm ↔
      nm * tm * nm⁻¹ * tm⁻¹ ∈ (zpowers z).subgroupOf (Mgrp z) := by
    have h1 : piq z nm * piq z tm = piq z (nm * tm) := (map_mul (piq z) nm tm).symm
    have h2 : piq z tm * piq z nm = piq z (tm * nm) := (map_mul (piq z) tm nm).symm
    rw [h1, h2]
    change ((nm * tm : ↥(Mgrp z)) : Xq z) = ((tm * nm : ↥(Mgrp z)) : Xq z) ↔
      nm * tm * nm⁻¹ * tm⁻¹ ∈ (zpowers z).subgroupOf (Mgrp z)
    rw [QuotientGroup.eq_iff_div_mem]
    have hdiv : (nm * tm) / (tm * nm) = nm * tm * nm⁻¹ * tm⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev]
      simp only [mul_assoc]
    rw [hdiv]
  rw [hker]
  have hmem : nm * tm * nm⁻¹ * tm⁻¹ ∈ (zpowers z).subgroupOf (Mgrp z) ↔
      (n : G) * t * (n : G)⁻¹ * t⁻¹ ∈ zpowers z := by
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((nm * tm * nm⁻¹ * tm⁻¹ : ↥(Mgrp z)) : G) =
        (n : G) * t * (n : G)⁻¹ * t⁻¹ := by
      rw [hnm, htm]
      rfl
    rw [hcoe]
  rw [hmem]
  have hconj : (n : G) * t * (n : G)⁻¹ * t⁻¹ ∈ zpowers z ↔
      ((n : G) * t * (n : G)⁻¹ = t ∨ (n : G) * t * (n : G)⁻¹ = t * z) := by
    constructor
    · intro hc
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
      have hord : orderOf z = 2 := orderOf_eq_prime h.z_sq h.z_ne_one
      have hk' : z ^ k = 1 ∨ z ^ k = z := by
        rw [← zpow_mod_orderOf z k, hord]
        norm_num only [Nat.cast_ofNat]
        rcases Int.emod_two_eq_zero_or_one k with h0 | h1
        · left; rw [h0]; simp
        · right; rw [h1]; simp
      have hcz : (n : G) * t * (n : G)⁻¹ * t⁻¹ = 1 ∨
          (n : G) * t * (n : G)⁻¹ * t⁻¹ = z := by
        rw [← hk]; exact hk'
      rcases hcz with h1 | hz
      · left
        calc (n : G) * t * (n : G)⁻¹
            = ((n : G) * t * (n : G)⁻¹ * t⁻¹) * t := by group
          _ = 1 * t := by rw [h1]
          _ = t := one_mul t
      · right
        calc (n : G) * t * (n : G)⁻¹
            = ((n : G) * t * (n : G)⁻¹ * t⁻¹) * t := by group
          _ = z * t := by rw [hz]
          _ = t * z := h.t_mul_z_comm.symm
    · rintro (h1 | h2)
      · rw [h1]; simp
      · rw [h2]
        have htz' : t * z * t⁻¹ = z := by
          rw [h.t_mul_z_comm]; group
        rw [htz']
        exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  rw [hconj, mem_normalizer_V_iff_mem_normalizer_Rgrp h hzt htz]
  exact ⟨fun hh => ⟨n.2, hh⟩, fun hh => hh.2⟩

theorem stab_Aq (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) (hs : Lemma27Spec h φ) :
    Nonempty (↥(Subgroup.map (psiq h hs) (centralizer
      ({(⟨wq h, Subgroup.le_normalizer (wq_mem_Aq h)⟩ : ↥(normalizer (Aq h : Set (Xq z))))} :
        Set ↥(normalizer (Aq h : Set (Xq z)))))) ≃* Equiv.Perm (Fin 5)) := by
  have hmap : Subgroup.map (psiq h hs) (centralizer
      ({(⟨wq h, Subgroup.le_normalizer (wq_mem_Aq h)⟩ : ↥(normalizer (Aq h : Set (Xq z))))} :
        Set ↥(normalizer (Aq h : Set (Xq z))))) =
      Subgroup.map φ (Subgroup.subgroupOf (NVgrp t z) (normalizer (Rgrp h : Set G))) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨n, rfl⟩ := piN_surjective h c
      rw [Subgroup.mem_map]
      refine ⟨n, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact (piN_mem_centralizer_iff h hzt htz n).mp hc
      · exact (psiq_piN h hs n).symm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨n, hn, rfl⟩ := hx
      rw [Subgroup.mem_map]
      refine ⟨piN h n, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hn
        exact (piN_mem_centralizer_iff h hzt htz n).mpr hn
      · exact psiq_piN h hs n
  rw [hmap]
  exact hs.stab

end CFSG.EvenSporadicStandard.HNRecog.Harada

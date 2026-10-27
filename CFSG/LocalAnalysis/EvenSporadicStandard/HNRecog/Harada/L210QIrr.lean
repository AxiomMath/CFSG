module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QL28
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Rep

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)
  {φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo}

theorem Rgrp_irreducible (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) (hs : Lemma27Spec h φ)
    {B : Subgroup G} (hBR : B ≤ Rgrp h) (hzB : z ∈ B)
    (hB : ∀ n ∈ normalizer (Rgrp h : Set G), ∀ b ∈ B, n * b * n⁻¹ ∈ B) :
    B = zpowers z ∨ B = Rgrp h := by
  have hBM : B ≤ Mgrp z := hBR.trans (Rgrp_le_Mgrp h)
  let Bbar : Subgroup (Xq z) := (B.subgroupOf (Mgrp z)).map (piq z)
  have hBA : Bbar ≤ Aq h := by
    rw [Aq]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono (Mgrp z) hBR)
  have hBinvar : ∀ y : ↥(normalizer (Aq h : Set (Xq z))),
      psiq h hs y ∈ commutator A5WrTwo →
      ∀ b ∈ Bbar, (y : Xq z) * b * (y : Xq z)⁻¹ ∈ Bbar := by
    intro y _ b hb
    obtain ⟨n, rfl⟩ := piN_surjective h y
    change b ∈ (B.subgroupOf (Mgrp z)).map (piq z) at hb
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hb
    rw [piN_val h n]
    have hmem : (⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩ : ↥(Mgrp z)) * m *
        (⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩ : ↥(Mgrp z))⁻¹ ∈
          B.subgroupOf (Mgrp z) := by
      rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        hB (n : G) n.2 (m : G) (Subgroup.mem_subgroupOf.mp hm)
    simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem (piq z) hmem
  rcases L28_irreducible (l28Hyp_Aq h hzt htz hs) hBA hBinvar with hbot | htop
  ·
    left
    apply le_antisymm
    · intro b hb
      have hmem : (⟨b, hBM hb⟩ : ↥(Mgrp z)) ∈ B.subgroupOf (Mgrp z) :=
        Subgroup.mem_subgroupOf.mpr hb
      have hb_bar : piq z ⟨b, hBM hb⟩ ∈ Bbar := Subgroup.mem_map_of_mem (piq z) hmem
      have hb_one : piq z ⟨b, hBM hb⟩ = 1 := by
        have h := hb_bar
        rw [hbot] at h
        exact Subgroup.mem_bot.mp h
      have hker : (⟨b, hBM hb⟩ : ↥(Mgrp z)) ∈ (piq z).ker := MonoidHom.mem_ker.mpr hb_one
      rw [ker_piq] at hker
      exact Subgroup.mem_subgroupOf.mp hker
    · exact Subgroup.zpowers_le.mpr hzB
  ·
    right
    apply le_antisymm hBR
    intro r hr
    have hrM : r ∈ Mgrp z := Rgrp_le_Mgrp h hr
    have hrb : piq z ⟨r, hrM⟩ ∈ Bbar := by
      rw [htop]
      exact (mem_Aq_iff h ⟨r, hrM⟩).mpr hr
    change piq z ⟨r, hrM⟩ ∈ (B.subgroupOf (Mgrp z)).map (piq z) at hrb
    obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp hrb
    have hker : m⁻¹ * ⟨r, hrM⟩ ∈ (piq z).ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, hmeq, inv_mul_cancel]
    have hzp : ((m⁻¹ * ⟨r, hrM⟩ : ↥(Mgrp z)) : G) ∈ zpowers z := by
      rw [ker_piq] at hker
      exact Subgroup.mem_subgroupOf.mp hker
    have hzB_le : zpowers z ≤ B := Subgroup.zpowers_le.mpr hzB
    have hmemB : (m : G)⁻¹ * r ∈ B := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hzB_le hzp
    have hmB : (m : G) ∈ B := Subgroup.mem_subgroupOf.mp hm
    have hr_eq : r = (m : G) * ((m : G)⁻¹ * r) := by group
    rw [hr_eq]
    exact mul_mem hmB hmemB

end CFSG.EvenSporadicStandard.HNRecog.Harada

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAutFrame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCentT

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem centTA_of_setting {G : Type} [Group G] [Finite G] {L : Subgroup G} (hS : HRSetting G L)
    (s : Setting3 G L) (hA : LFactsA s) (h31 : s.Fact31)
    (hOut : (innerAut (L ⧸ center L)).index = 2) : centIn s.T s.fr.A = zt s := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  apply le_antisymm
  ·
    intro x hx
    rw [centIn] at hx
    obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ normalizer (L : Set G) := s3_T_le_N s hS hxT
    let α : MulAut (L ⧸ center L) := jHom L ⟨x, hxN⟩
    have hxacts : ActsAs L x α := jHom_actsAs L ⟨x, hxN⟩
    have hcomm : ∀ a' ∈ s.fr'.A, ⁅a', α⁆ ∈ s.fr'.Z := by
      intro a' ha'
      rw [← s3_jSub_A s] at ha'
      obtain ⟨a, haA, haacts⟩ := (mem_jSub L).mp ha'
      have hcomm_acts : ActsAs L ⁅a, x⁆ ⁅a', α⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        exact actsAs_mul L (actsAs_mul L (actsAs_mul L haacts hxacts)
          (actsAs_inv L haacts)) (actsAs_inv L hxacts)
      have hcomm_one : ⁅a, x⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_centralizer_iff.mp hxC a haA
      rw [hcomm_one] at hcomm_acts
      have huniq : ⁅a', α⁆ = 1 := actsAs_unique L hcomm_acts (actsAs_one L)
      rw [huniq]
      exact Subgroup.one_mem _
    have hαA : α ∈ s.fr'.A := frame_centralizer_A s.fr' s.facts hOut hcomm
    rw [← s3_jSub_A s] at hαA
    obtain ⟨a, haA, haacts⟩ := (mem_jSub L).mp hαA
    have hprodActs : ActsAs L (a⁻¹ * x) (α⁻¹ * α) :=
      actsAs_mul L (actsAs_inv L haacts) hxacts
    have hprodActs1 : ActsAs L (a⁻¹ * x) 1 := by simpa using hprodActs
    have hker : a⁻¹ * x ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hprodActs1
    have hprodT : a⁻¹ * x ∈ s.T :=
      Subgroup.mul_mem s.T (Subgroup.inv_mem s.T (s3_A_le_T s haA)) hxT
    have hzpow : a⁻¹ * x ∈ zpowers s.t := by
      have h : a⁻¹ * x ∈ s.T ⊓ centralizer (L : Set G) := Subgroup.mem_inf.mpr ⟨hprodT, hker⟩
      rwa [s3_T_inf_centralizer s h31] at h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzpow
    have hx_eq : x = a * s.t ^ k := by
      rw [hk]
      group
    have htC : s.t ∈ centralizer (s.fr.A : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun b hb => s3_comm_t_of_mem_A s hb)
    have htkC : s.t ^ k ∈ centralizer (s.fr.A : Set G) :=
      Subgroup.zpow_mem _ htC k
    have haC : a ∈ centralizer (s.fr.A : Set G) := by
      have ha_eq : a = x * (s.t ^ k)⁻¹ := by rw [hx_eq]; group
      rw [ha_eq]
      exact Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ htkC)
    have haZ : a ∈ s.fr.Z := by
      have h : a ∈ cen s.fr.A := Subgroup.mem_inf.mpr ⟨haA, haC⟩
      rwa [hA.cen_A] at h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp haZ
    rw [hx_eq, ← hj]
    exact Subgroup.mul_mem _
      (Subgroup.zpow_mem (zt s) (Subgroup.subset_closure (by simp)) j)
      (Subgroup.zpow_mem (zt s) (Subgroup.subset_closure (by simp)) k)
  ·
    rw [centIn]
    exact le_inf (s3_zt_le_T s) (s3_zt_le_cent_A s hA)

theorem centTA_of (h31 : Fusion31) (hZ : OddCentre) (hOut : OutTwo) : CentTA :=
  fun G _ _ L hS hL s =>
    centTA_of_setting hS s (lfactsA_of_setting hS (hZ G L hS hL) s) (h31 G L hS hL s)
      (hOut _ hL)

end CFSG.OddStandard.HigherRank.YamadaG23

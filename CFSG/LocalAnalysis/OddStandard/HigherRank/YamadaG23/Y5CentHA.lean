module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAutFrame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y5_centHA {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    centIn s.H s.fr.A = zt s := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hH.hS
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  apply le_antisymm
  ·
    intro x hx
    rw [centIn] at hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ normalizer (L : Set G) := s3_H_le_N s hH.hS hxH
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
    have hαA : α ∈ s.fr'.A := frame_centralizer_A s.fr' s.facts hH.hOut hcomm
    rw [← s3_jSub_A s] at hαA
    obtain ⟨a, haA, haacts⟩ := (mem_jSub L).mp hαA
    have hprodActs : ActsAs L (a⁻¹ * x) (α⁻¹ * α) :=
      actsAs_mul L (actsAs_inv L haacts) hxacts
    have hprodActs1 : ActsAs L (a⁻¹ * x) 1 := by simpa using hprodActs
    have hker : a⁻¹ * x ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hprodActs1
    have haH : a ∈ s.H := s3_L_le_H s hH.hS (s3_A_le_L s haA)
    have hprodH : a⁻¹ * x ∈ s.H :=
      Subgroup.mul_mem s.H (Subgroup.inv_mem s.H haH) hxH
    have hzpow : a⁻¹ * x ∈ zpowers s.t := by
      have h : a⁻¹ * x ∈ centIn s.H L := Subgroup.mem_inf.mpr ⟨hprodH, hker⟩
      rwa [f3_centIn_H_L hH] at h
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
    exact le_inf ((s3_zt_le_T s).trans s.sylow_T.1) (s3_zt_le_cent_A s hA)

end CFSG.OddStandard.HigherRank.YamadaG23

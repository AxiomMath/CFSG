module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UBasic
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGDefs

import CFSG.LocalAnalysis.OddStandard.SwapPartner.UTstar
import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGCent

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G}

theorem card_Agrp (F : UFrame z ι ιd) : Nat.card (Agrp ι) = 20160 := by
  rw [Agrp, Subgroup.card_map_of_injective (injective_comp_liftS8 F)]
  rw [nat_card_alternatingGroup (α := Fin 8), Nat.card_fin]
  norm_num [Nat.factorial]

theorem isPerfect_Agrp (F : UFrame z ι ιd) : Group.IsPerfect ↥(Agrp ι) := by
  haveI : Group.IsPerfect ↥(alternatingGroup (Fin 8)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (α := Fin 8) (by simp))
  rw [Agrp]
  exact Group.IsPerfect.map (ι.comp liftS8)

theorem Agrp_le_centralizer_of_frame (F : UFrame z ι ιd) :
    Agrp ι ≤ centralizer ({z * ι τ₀} : Set G) := by
  intro a ha
  rw [mem_centralizer_singleton_iff]
  obtain ⟨ρ, _, rfl⟩ := mem_Agrp_iff.1 ha
  have hzcomm : z * ι (liftS8 ρ) = ι (liftS8 ρ) * z := F.z_comm_sigma ρ
  have hτcomm : ι (liftS8 ρ) * ι τ₀ = ι τ₀ * ι (liftS8 ρ) := by
    rw [← map_mul, ← map_mul, liftS8_mul_τ₀]
  calc ι (liftS8 ρ) * (z * ι τ₀)
      = (ι (liftS8 ρ) * z) * ι τ₀ := by group
    _ = (z * ι (liftS8 ρ)) * ι τ₀ := by rw [← hzcomm]
    _ = z * (ι (liftS8 ρ) * ι τ₀) := by group
    _ = z * (ι τ₀ * ι (liftS8 ρ)) := by rw [hτcomm]
    _ = (z * ι τ₀) * ι (liftS8 ρ) := by group

theorem not_centralizes_z_of_card_gt (F : UFrame z ι ιd) {Kh : Subgroup G}
    (hle : Kh ≤ centralizer ({z * ι τ₀} : Set G)) (hperf : ⁅Kh, Kh⁆ = Kh) (hA : Agrp ι ≤ Kh)
    (hcard : 20160 < Nat.card ↥Kh) [Finite G] : ¬ ∀ k ∈ Kh, z * k = k * z := by
  intro hz
  have hx2eq : z * (z * ι τ₀) = ι τ₀ := by rw [← mul_assoc, F.cent.mul_self, one_mul]
  have hτ_comm : ∀ k ∈ Kh, k ∈ centralizer ({ι τ₀} : Set G) := by
    intro k hk
    have hkz : k * z = z * k := (hz k hk).symm
    have hkx : k * (z * ι τ₀) = (z * ι τ₀) * k :=
      mem_centralizer_singleton_iff.mp (hle hk)
    refine mem_centralizer_singleton_iff.mpr ?_
    calc k * ι τ₀ = k * (z * (z * ι τ₀)) := by rw [hx2eq]
      _ = (k * z) * (z * ι τ₀) := by rw [mul_assoc]
      _ = (z * k) * (z * ι τ₀) := by rw [hkz]
      _ = z * (k * (z * ι τ₀)) := by rw [mul_assoc]
      _ = z * ((z * ι τ₀) * k) := by rw [hkx]
      _ = ι τ₀ * k := by rw [← mul_assoc, hx2eq]
  have hKh_CE : Kh ≤ CEgrp z ι :=
    fun k hk => ⟨mem_centralizer_singleton_iff.mpr (hz k hk).symm, hτ_comm k hk⟩
  have hcomm_le : ⁅Kh, Kh⁆ ≤ Agrp ι := by
    have h := Subgroup.commutator_mono hKh_CE hKh_CE
    rwa [commutator_CEgrp F.cent] at h
  have hKh_le_A : Kh ≤ Agrp ι := by
    rw [← hperf]
    exact hcomm_le
  have hEq : Kh = Agrp ι := le_antisymm hKh_le_A hA
  have hcard_eq : Nat.card ↥Kh = 20160 := by rw [hEq, card_Agrp F]
  omega

end CFSG.OddStandard.AltStdSec.SwapPartner

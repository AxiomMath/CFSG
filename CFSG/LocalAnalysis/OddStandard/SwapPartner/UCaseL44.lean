module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UKhatZ
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UL44Glue

import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGCent
import CFSG.LocalAnalysis.OddStandard.SwapPartner.UTstar
import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UPerm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.Blueprint Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G}

theorem false_of_lieModel_l44 (F : UFrame z ι ιd) [Finite G] {Kh : Subgroup G}
    (hle : Kh ≤ centralizer ({z * ι τ₀} : Set G))
    (hn : (Kh.subgroupOf (centralizer ({z * ι τ₀} : Set G))).Normal) (hperf : ⁅Kh, Kh⁆ = Kh)
    (hA : Agrp ι ≤ Kh) (hS : LieModel (↥Kh ⧸ center ↥Kh) .PSL 4 2 2) : False := by
  classical
  have hcardQ : Nat.card (↥Kh ⧸ center ↥Kh) = 987033600 := by
    rw [CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hS]
    decide
  have hcard : 20160 < Nat.card ↥Kh := by
    have h := Nat.card_le_card_of_surjective (QuotientGroup.mk' (center ↥Kh))
      (QuotientGroup.mk'_surjective (center ↥Kh))
    rw [hcardQ] at h
    omega
  have ht1 : ¬ ∀ n ∈ Kh, z * n = n * z :=
    not_centralizes_z_of_card_gt F hle hperf hA hcard
  let eA : ↥(Agrp ι) ≃* alternatingGroup (Fin 8) :=
    (Subgroup.equivMapOfInjective (alternatingGroup (Fin 8)) (ι.comp liftS8)
      (injective_comp_liftS8 F)).symm
  have htA : ∀ a ∈ Agrp ι, z * a = a * z := by
    intro a ha
    obtain ⟨ρ, -, rfl⟩ := (mem_Agrp_iff).mp ha
    exact F.z_comm_sigma ρ
  set d : G := ι (swap 0 1) with hd_def
  have hd : d ∈ centralizer ({z * ι τ₀} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hz : d * z = z * d := (F.cent.comm (swap 0 1)).symm
    have hτ : d * ι τ₀ = ι τ₀ * d := by
      have hp : (swap (0 : Fin 10) 1) * τ₀ = τ₀ * swap (0 : Fin 10) 1 := by decide
      rw [hd_def]
      calc ι (swap 0 1) * ι τ₀ = ι (swap 0 1 * τ₀) := by rw [map_mul]
        _ = ι (τ₀ * swap 0 1) := by rw [hp]
        _ = ι τ₀ * ι (swap 0 1) := by rw [map_mul]
    calc d * (z * ι τ₀) = (d * z) * ι τ₀ := by group
      _ = (z * d) * ι τ₀ := by rw [hz]
      _ = z * (d * ι τ₀) := by group
      _ = z * (ι τ₀ * d) := by rw [hτ]
      _ = (z * ι τ₀) * d := by group
  have hd2 : d * d = 1 := by
    rw [hd_def, ← map_mul, Equiv.swap_mul_self, map_one]
  have hdt : d * z = z * d := (F.cent.comm (swap 0 1)).symm
  have hdA : ∀ a ∈ Agrp ι, d * a * d⁻¹ ∈ Agrp ι := by
    intro a ha
    obtain ⟨ρ, hρ, rfl⟩ := (mem_Agrp_iff).mp ha
    have h_d : d = ι (liftS8 (swap (0 : Fin 8) 1)) := by
      rw [hd_def, liftS8_swap_zero_one]
    have hconj : swap (0 : Fin 8) 1 * ρ * (swap (0 : Fin 8) 1)⁻¹ ∈ alternatingGroup (Fin 8) :=
      (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem ρ hρ (swap 0 1)
    refine (mem_Agrp_iff).mpr
      ⟨swap (0 : Fin 8) 1 * ρ * (swap (0 : Fin 8) 1)⁻¹, hconj, ?_⟩
    rw [h_d]
    simp only [← map_mul, ← map_inv]
  have hdout : ¬ ∃ a ∈ Agrp ι, ∀ y ∈ Agrp ι, d * y * d⁻¹ = a * y * a⁻¹ := by
    rintro ⟨a, ha, ha'⟩
    obtain ⟨ρ, hρ, rfl⟩ := (mem_Agrp_iff).mp ha
    set b : G := ι (liftS8 (ρ⁻¹ * swap (0 : Fin 8) 1)) with hb_def
    have hb_eq : b = (ι (liftS8 ρ))⁻¹ * d := by
      rw [hb_def, hd_def]
      simp only [map_mul, map_inv, liftS8_swap_zero_one]
    have hbS : b ∈ Siggrp ι := (mem_Siggrp_iff).mpr ⟨ρ⁻¹ * swap (0 : Fin 8) 1, rfl⟩
    have hbCE : b ∈ CEgrp z ι := Siggrp_le_CEgrp F.cent hbS
    have hbA : b ∈ centralizer (Agrp ι : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have hconj : d * y * d⁻¹ = (ι (liftS8 ρ)) * y * (ι (liftS8 ρ))⁻¹ := ha' y hy
      have hby : b * y * b⁻¹ = y := by
        rw [hb_eq]
        calc ((ι (liftS8 ρ))⁻¹ * d) * y * ((ι (liftS8 ρ))⁻¹ * d)⁻¹
            = (ι (liftS8 ρ))⁻¹ * (d * y * d⁻¹) * (ι (liftS8 ρ)) := by group
          _ = (ι (liftS8 ρ))⁻¹ * ((ι (liftS8 ρ)) * y * (ι (liftS8 ρ))⁻¹) *
                (ι (liftS8 ρ)) := by rw [hconj]
          _ = y := by group
      calc y * b = (b * y * b⁻¹) * b := by rw [hby]
        _ = b * y := by group
    have hbE : b ∈ Egrp z ι := by
      have h1 : b ∈ centralizer (Agrp ι : Set G) ⊓ CEgrp z ι :=
        Subgroup.mem_inf.mpr ⟨hbA, hbCE⟩
      rwa [centralizer_Agrp_inf_CEgrp F.cent] at h1
    have hb1 : b = 1 := by
      have h1 : b ∈ Egrp z ι ⊓ Siggrp ι := Subgroup.mem_inf.mpr ⟨hbE, hbS⟩
      rw [Egrp_inf_Siggrp F.cent] at h1
      simpa using h1
    have hd_eq_a : d = ι (liftS8 ρ) := by
      have hthis : (ι (liftS8 ρ))⁻¹ * d = 1 := by rw [← hb_eq, hb1]
      calc d = (ι (liftS8 ρ)) * ((ι (liftS8 ρ))⁻¹ * d) := by group
        _ = (ι (liftS8 ρ)) * 1 := by rw [hthis]
        _ = ι (liftS8 ρ) := mul_one _
    have hperm : swap (0 : Fin 8) 1 = ρ := by
      have h1 : ι (swap (0 : Fin 10) 1) = ι (liftS8 ρ) := by
        rw [← hd_def]; exact hd_eq_a
      have h2 : swap (0 : Fin 10) 1 = liftS8 ρ := F.cent.inj h1
      have h3 : liftS8 (swap (0 : Fin 8) 1) = liftS8 ρ := by
        rw [liftS8_swap_zero_one]; exact h2
      exact liftS8_injective h3
    rw [← hperm] at hρ
    rw [Equiv.Perm.mem_alternatingGroup,
      Equiv.Perm.sign_swap (by decide : (0 : Fin 8) ≠ 1)] at hρ
    exact absurd hρ (by decide)
  have hge := card_inf_centralizer_ge_of_lieModel_l44 (x := z * ι τ₀) (N := Kh)
    (A := Agrp ι) hle hn hperf hS hA eA (t := z) (d := ι (swap 0 1))
    (z_mem_centralizer_x₂ F.cent) hd ht1 F.cent.mul_self htA hd2 hdt hdA hdout
  have heq : Nat.card ↥(centralizer ({ι (swap 0 1)} : Set G) ⊓
      centralizer ({z * ι τ₀} : Set G)) = N10 2 := by
    change pairOrder (ι (swap 0 1)) (z * ι τ₀) = N10 2
    exact F.pairOrder_d_x₂
  have hN : N10 2 = 11520 := by norm_num [N10, Nat.factorial]
  rw [heq, hN] at hge
  omega

end CFSG.OddStandard.AltStdSec.SwapPartner

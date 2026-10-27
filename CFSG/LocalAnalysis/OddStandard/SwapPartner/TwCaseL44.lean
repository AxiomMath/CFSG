module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwL44G
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwL44Frame
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwAgrp
import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.Blueprint Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem tw_liftS8_swap01 :
    liftS8 (swap 0 1 : Perm (Fin 8)) = (swap 0 1 : Perm (Fin 10)) := by
  rw [liftS8_swap]
  rfl

private theorem tw_swap01_mul_tau0 :
    (swap 0 1 : Perm (Fin 10)) * τ₀ = τ₀ * swap 0 1 := by
  ext i
  fin_cases i <;> decide

private theorem tw_conj_iota_liftS8 (ι : Perm (Fin 10) →* G) (σ τ : Perm (Fin 8)) :
    ι (liftS8 σ) * ι (liftS8 τ) * (ι (liftS8 σ))⁻¹ = ι (liftS8 (σ * τ * σ⁻¹)) := by
  simp only [map_mul, map_inv]

theorem not_centralizes_z_of_ne_agrp (hC : CentData z ι) {Kh : Subgroup G}
    (hle : Kh ≤ centralizer ({z * ι τ₀} : Set G)) (hperf : ⁅Kh, Kh⁆ = Kh)
    (hA : Agrp ι ≤ Kh) (hne : Kh ≠ Agrp ι) : ¬ ∀ k ∈ Kh, z * k = k * z := by
  intro hzcent
  have hle_z : Kh ≤ centralizer ({z} : Set G) := by
    intro k hk
    rw [mem_centralizer_singleton_iff]
    exact (hzcent k hk).symm
  have hle_CE : Kh ≤ CEgrp z ι := by
    intro k hk
    rw [CEgrp, Subgroup.mem_inf]
    refine ⟨hle_z hk, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hkz : Commute k z := mem_centralizer_singleton_iff.mp (hle_z hk)
    have hkx : Commute k (z * ι τ₀) := mem_centralizer_singleton_iff.mp (hle hk)
    have hz2 : z * (z * ι τ₀) = ι τ₀ := by rw [← mul_assoc, hC.mul_self, one_mul]
    have h := hkz.mul_right hkx
    rwa [hz2] at h
  have hcomm : ⁅Kh, Kh⁆ ≤ ⁅CEgrp z ι, CEgrp z ι⁆ :=
    Subgroup.commutator_mono hle_CE hle_CE
  rw [commutator_CEgrp hC] at hcomm
  have hle' : Kh ≤ Agrp ι := by rwa [hperf] at hcomm
  exact hne (le_antisymm hle' hA)

theorem false_of_lieModel_l44_twisted [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 2)
    {Kh : Subgroup G} (hle : Kh ≤ centralizer ({z * ι τ₀} : Set G))
    (hn : (Kh.subgroupOf (centralizer ({z * ι τ₀} : Set G))).Normal) (hperf : ⁅Kh, Kh⁆ = Kh)
    (hA : Agrp ι ≤ Kh) (hz : ¬ ∀ k ∈ Kh, z * k = k * z)
    (hS : LieModel (↥Kh ⧸ center ↥Kh) .PSL 4 2 2) : False := by
  obtain ⟨eA⟩ := nonempty_mulEquiv_Agrp hC
  have hd : ι (swap 0 1) ∈ centralizer ({z * ι τ₀} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc ι (swap 0 1) * (z * ι τ₀)
        = (ι (swap 0 1) * z) * ι τ₀ := by rw [← mul_assoc]
      _ = (z * ι (swap 0 1)) * ι τ₀ := by rw [(hC.comm (swap 0 1)).symm]
      _ = z * (ι (swap 0 1) * ι τ₀) := by rw [mul_assoc]
      _ = z * (ι ((swap 0 1) * τ₀)) := by rw [← map_mul]
      _ = z * (ι (τ₀ * swap 0 1)) := by rw [tw_swap01_mul_tau0]
      _ = z * (ι τ₀ * ι (swap 0 1)) := by rw [map_mul]
      _ = (z * ι τ₀) * ι (swap 0 1) := by rw [mul_assoc]
  have htA : ∀ a ∈ Agrp ι, z * a = a * z := by
    intro a ha
    obtain ⟨ρ, -, rfl⟩ := (mem_Agrp_iff).mp ha
    exact hC.comm (liftS8 ρ)
  have hd2 : ι (swap 0 1) * ι (swap 0 1) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self (0 : Fin 10) 1, map_one]
  have hdt : ι (swap 0 1) * z = z * ι (swap 0 1) := (hC.comm (swap 0 1)).symm
  have hdA : ∀ a ∈ Agrp ι, ι (swap 0 1) * a * (ι (swap 0 1))⁻¹ ∈ Agrp ι := by
    intro a ha
    obtain ⟨ρ, hρ, rfl⟩ := (mem_Agrp_iff).mp ha
    rw [show ι (swap 0 1) = ι (liftS8 (swap 0 1 : Perm (Fin 8))) from by
      rw [tw_liftS8_swap01]]
    rw [tw_conj_iota_liftS8]
    refine (mem_Agrp_iff).mpr ⟨(swap 0 1 : Perm (Fin 8)) * ρ * (swap 0 1)⁻¹, ?_, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_inv,
      Equiv.Perm.mem_alternatingGroup.mp hρ]
    group
  have hdout : ¬ ∃ a ∈ Agrp ι, ∀ y ∈ Agrp ι,
      ι (swap 0 1) * y * (ι (swap 0 1))⁻¹ = a * y * a⁻¹ := by
    rintro ⟨a, ha, ha_act⟩
    obtain ⟨α, hα, rfl⟩ := (mem_Agrp_iff).mp ha
    have hconj : ∀ ρ ∈ alternatingGroup (Fin 8),
        (swap 0 1 : Perm (Fin 8)) * ρ * (swap 0 1)⁻¹ = α * ρ * α⁻¹ := by
      intro ρ hρ
      have h := ha_act (ι (liftS8 ρ)) ((mem_Agrp_iff).mpr ⟨ρ, hρ, rfl⟩)
      rw [← tw_liftS8_swap01] at h
      simp only [tw_conj_iota_liftS8] at h
      exact liftS8_injective (hC.inj h)
    have hβ : ∀ ρ ∈ alternatingGroup (Fin 8),
        (α⁻¹ * (swap 0 1 : Perm (Fin 8))) * ρ = ρ * (α⁻¹ * (swap 0 1)) := by
      intro ρ hρ
      have h := hconj ρ hρ
      calc (α⁻¹ * (swap 0 1)) * ρ
          = α⁻¹ * ((swap 0 1) * ρ * (swap 0 1)⁻¹) * (swap 0 1) := by group
        _ = α⁻¹ * (α * ρ * α⁻¹) * (swap 0 1) := by rw [h]
        _ = ρ * (α⁻¹ * (swap 0 1)) := by group
    have hβbot : (α⁻¹ * (swap 0 1 : Perm (Fin 8))) ∈
        Subgroup.centralizer (alternatingGroup (Fin 8) : Set (Perm (Fin 8))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro ρ hρ
      exact (hβ ρ hρ).symm
    have hβone : α⁻¹ * (swap 0 1 : Perm (Fin 8)) = 1 := by
      have hbot :=
        CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
          (α := Fin 8) (by rw [Nat.card_fin]; norm_num : 4 ≤ Nat.card (Fin 8))
      rw [hbot] at hβbot
      exact Subgroup.mem_bot.mp hβbot
    have hsα : (swap 0 1 : Perm (Fin 8)) = α := by
      have := congrArg (fun x => α * x) hβone
      simpa using this
    have hs_ne : (swap 0 1 : Perm (Fin 8)) ∉ alternatingGroup (Fin 8) := by
      intro hs
      have h1 : Equiv.Perm.sign (swap 0 1 : Perm (Fin 8)) = 1 :=
        Equiv.Perm.mem_alternatingGroup.mp hs
      rw [Equiv.Perm.sign_swap (by decide : (0 : Fin 8) ≠ 1)] at h1
      exact absurd h1 (Int.units_ne_iff_eq_neg.mpr rfl)
    exact hs_ne (hsα.symm ▸ hα)
  have h7 := seven_dvd_card_inf_of_lieModel_l44 (N := Kh) (A := Agrp ι) hle hn hperf hS hA
    eA.symm (z_mem_centralizer_x₂ hC) hd hz hC.mul_self htA hd2 hdt hdA hdout
    (seven_dvd_card_pair_d_x₂ hC hx hP2 hp)
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card' (G :=
    ↥(centralizer ({ι (swap 0 1)} : Set G) ⊓ centralizer ({z * ι τ₀} : Set G) ⊓
      centralizer (Kh : Set G))) 7 h7
  have hu_d : (u : G) ∈ centralizer ({ι (swap 0 1)} : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp u.2).1).1
  have hu_Kh : (u : G) ∈ centralizer (Kh : Set G) := (Subgroup.mem_inf.mp u.2).2
  have huordG : orderOf (u : G) = 7 := (Subgroup.orderOf_coe u).trans huord
  have hu7 : (u : G) ^ 7 = 1 := by
    rw [← huordG]
    exact pow_orderOf_eq_one (u : G)
  have hcomm : ∀ ρ ∈ alternatingGroup (Fin 8), ρ 0 = 0 → ρ 1 = 1 →
      (u : G) * ι (liftS8 ρ) = ι (liftS8 ρ) * (u : G) := by
    intro ρ hρ _ _
    have hmem : ι (liftS8 ρ) ∈ Kh := hA ((mem_Agrp_iff).mpr ⟨ρ, hρ, rfl⟩)
    exact ((Subgroup.mem_centralizer_iff.mp hu_Kh) (ι (liftS8 ρ)) hmem).symm
  have hu1 : (u : G) = 1 := eq_one_of_pow_seven_of_commute hC hx hP2 hp hu_d hu7 hcomm
  rw [hu1, orderOf_one] at huordG
  exact absurd huordG (by norm_num)

end CFSG.OddStandard.AltStdSec.SwapPartner

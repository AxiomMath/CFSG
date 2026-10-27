module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.AbstractBar

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Abstract

variable {Γ : Type*} [Group Γ] {R : Subgroup Γ} [R.Normal] {z : Γ}

theorem BarCfg.free_mod_z [Finite Γ] (c : BarCfg R z) (X : Sylow 3 Γ) {x₀ : Γ}
    (hX : (X : Subgroup Γ) = zpowers x₀) (hx3 : x₀ ^ 3 = 1) {e : Γ} (he : e ∈ R)
    (hez : e ∉ zpowers z) : e⁻¹ * (x₀ * e * x₀⁻¹) ∉ zpowers z := by
  intro hmem
  have hQx : ∀ q ∈ zpowers z, x₀ * q * x₀⁻¹ ∈ zpowers z := by
    rintro _ ⟨n, rfl⟩
    have h1 : x₀ * z ^ n = z ^ n * x₀ :=
      (Commute.zpow_right (show Commute x₀ z from c.z_central x₀) n).eq
    have h2 : x₀ * z ^ n * x₀⁻¹ = z ^ n := by rw [h1]; group
    rw [h2]
    exact ⟨n, rfl⟩
  have hc : e⁻¹ * x₀ * e * x₀⁻¹ ∈ zpowers z := by
    have : e⁻¹ * x₀ * e * x₀⁻¹ = e⁻¹ * (x₀ * e * x₀⁻¹) := by group
    rw [this]
    exact hmem
  have h3 : ¬ 3 ∣ Nat.card (zpowers z) := by
    rw [Nat.card_zpowers]
    intro h
    have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact c.z_sq)
    have := Nat.le_of_dvd (by norm_num) (h.trans h2)
    omega
  obtain ⟨q, hq, hfix⟩ := exists_fixed_coset (zpowers z) x₀ e hx3 hQx hc h3
  have hzR : zpowers z ≤ R := zpowers_le.2 c.z_mem
  have hrq : e * q ∈ R := R.mul_mem he (hzR hq)
  have hcomm : ∀ w ∈ (X : Subgroup Γ), w * (e * q) = (e * q) * w := by
    intro w hw
    rw [hX] at hw
    obtain ⟨n, rfl⟩ := hw
    exact (Commute.zpow_left (show Commute x₀ (e * q) from hfix) n).eq
  have hmemz : e * q ∈ zpowers z := c.cent_X X (e * q) hrq hcomm
  apply hez
  have : e = (e * q) * q⁻¹ := by group
  rw [this]
  exact mul_mem hmemz (inv_mem hq)

theorem mem_zpowers_involution {g : Γ} (hz : z * z = 1) :
    g ∈ zpowers z ↔ g = 1 ∨ g = z := by
  constructor
  · rintro ⟨n, rfl⟩
    show z ^ n = 1 ∨ z ^ n = z
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
    rw [zpow_eq_zpow_emod n h2]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

end Abstract

end CFSG.GH74.GLS.Stage1.Thm6.Prod

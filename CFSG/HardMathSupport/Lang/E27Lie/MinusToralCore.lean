module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnCard
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E27Lie

open Subgroup CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {Y : Type*} [Group Y] [Finite Y]

theorem card_zpowers_sup_zpowers_of_order_three {u₁ u₂ : Y} (hc : u₁ * u₂ = u₂ * u₁)
    (h₁ : u₁ ^ 3 = 1) (h₁' : u₁ ≠ 1) (h₂ : u₂ ^ 3 = 1) (h₂' : u₂ ∉ zpowers u₁) :
    Nat.card ↥(zpowers u₁ ⊔ zpowers u₂) = 9 := by
  have hord : orderOf u₁ = 3 := orderOf_eq_prime h₁ h₁'
  have hcard : Nat.card ↥(zpowers u₁) = 3 := by rw [Nat.card_zpowers, hord]
  have hn : ∀ t ∈ zpowers u₁, u₂ * t * u₂⁻¹ ∈ zpowers u₁ := by
    intro t ht
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
    have : Commute u₂ u₁ := hc.symm
    rw [(this.zpow_right k).eq, mul_inv_cancel_right]
    exact zpow_mem_zpowers u₁ k
  have h3 : u₂ ^ 3 ∈ zpowers u₁ := by rw [h₂]; exact one_mem _
  have := card_sup_zpowers_of_cube_mem hn h3 h₂'
  rw [sup_comm] at this
  rw [sup_comm, this, hcard]

theorem dvd_card_of_torus_lift {φ : MulAut Y} {C : Subgroup Y} (hC : ∀ x, x ∈ C ↔ φ x = x)
    {T : Subgroup Y} {m u₁ u₂ : Y} (hm : ∀ t ∈ T, m * t * m⁻¹ ∈ T) (hm3 : m ^ 3 ∈ T)
    (hmT : m ∉ T) (hmφ : φ m = m) (hu₁ : u₁ ∈ T) (hu₂ : u₂ ∈ T) (hu₁φ : φ u₁ = u₁)
    (hu₂φ : φ u₂ = u₂) (hc : u₁ * u₂ = u₂ * u₁) (h₁ : u₁ ^ 3 = 1) (h₁' : u₁ ≠ 1)
    (h₂ : u₂ ^ 3 = 1) (h₂' : u₂ ∉ zpowers u₁) : 27 ∣ Nat.card C := by
  set A : Subgroup Y := C ⊓ T with hA
  have h9 : 9 ∣ Nat.card A := by
    have hle : zpowers u₁ ⊔ zpowers u₂ ≤ A := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · exact mem_inf.2 ⟨(hC _).2 hu₁φ, hu₁⟩
      · exact mem_inf.2 ⟨(hC _).2 hu₂φ, hu₂⟩
    rw [← card_zpowers_sup_zpowers_of_order_three hc h₁ h₁' h₂ h₂']
    exact Subgroup.card_dvd_of_le hle
  have hmA : ∀ t ∈ A, m * t * m⁻¹ ∈ A := by
    intro t ht
    obtain ⟨htC, htT⟩ := mem_inf.1 ht
    refine mem_inf.2 ⟨(hC _).2 ?_, hm t htT⟩
    rw [map_mul, map_mul, map_inv, hmφ, ((hC t).1 htC)]
  have hm3A : m ^ 3 ∈ A := by
    refine mem_inf.2 ⟨(hC _).2 ?_, hm3⟩
    rw [map_pow, hmφ]
  have hmA' : m ∉ A := fun h => hmT (mem_inf.1 h).2
  have hcard := card_sup_zpowers_of_cube_mem hmA hm3A hmA'
  have hle : A ⊔ zpowers m ≤ C := by
    refine sup_le inf_le_left (zpowers_le.2 ((hC _).2 hmφ))
  have h27 : 27 ∣ Nat.card ↥(A ⊔ zpowers m) := by
    rw [hcard]
    obtain ⟨k, hk⟩ := h9
    rw [hk]
    exact ⟨k, by ring⟩
  exact h27.trans (Subgroup.card_dvd_of_le hle)

end CFSG.HardMathSupport.Lang.E27Lie

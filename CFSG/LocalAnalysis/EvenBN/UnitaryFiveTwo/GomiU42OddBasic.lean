module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Free
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Setup

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.not_mem_E (h : GomiU42Data X J D E a) : a ∉ E := by
  intro haE
  haveI := h.elementary
  have h1 : E ⊓ centralizer ({a} : Set X) = E := by
    apply le_antisymm inf_le_left
    refine le_inf le_rfl fun x hx => ?_
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥E)).comm ⟨x, hx⟩ ⟨a, haE⟩)
  have h2 := h.card_centralizer_E
  rw [h1, h.card_E] at h2
  norm_num at h2

theorem GomiU42Data.card_centralizer (h : GomiU42Data X J D E a) :
    Nat.card (centralizer ({a} : Set X)) = 51840 := by
  have hJn : J ≤ normalizer (zpowers a : Set X) := by
    intro x hx
    have hc : ∀ y ∈ zpowers a, x * y = y * x := by
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_right (show Commute x a from (h.commute_of_mem_J hx).symm) k).eq
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : x * y * x⁻¹ = y := by rw [hc y hy]; group
      rw [this]
      exact hy
    · intro hy
      have hzx := hc _ hy
      have : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = x⁻¹ * ((x * y * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [← hzx]
          _ = x * y * x⁻¹ := by group
      rw [this]
      exact hy
  have hprod := GomiU42Setup.card_sup_mul_card_inf_of_le_normalizer' (zpowers a) J hJn
  rw [h.sup_eq, h.inf_eq_bot, Subgroup.card_bot, mul_one, Nat.card_zpowers, h.orderOf_a,
    h.card_J] at hprod
  rw [hprod]

theorem GomiU42Data.two_pow_nine_dvd (h : GomiU42Data X J D E a) : 2 ^ 9 ∣ Nat.card X := by
  have hEn : zpowers a ≤ normalizer (E : Set X) := by
    rw [zpowers_le]
    exact h.mem_normalizer
  have hinf : E ⊓ zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxa⟩ := mem_inf.1 hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxa
    have hk : a ^ (k % 2) = a ^ k := by
      have := zpow_mod_orderOf a k
      rwa [h.orderOf_a, Nat.cast_ofNat] at this
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [← hk, h0, zpow_zero]
      exact one_mem _
    · exfalso
      apply h.not_mem_E
      rw [← hk, h1, zpow_one] at hxE
      exact hxE
  have hprod := GomiU42Setup.card_sup_mul_card_inf_of_le_normalizer' E (zpowers a) hEn
  rw [hinf, Subgroup.card_bot, mul_one, h.card_E, Nat.card_zpowers, h.orderOf_a] at hprod
  have hdvd := Subgroup.card_subgroup_dvd_card (E ⊔ zpowers a)
  rw [hprod] at hdvd
  exact hdvd

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

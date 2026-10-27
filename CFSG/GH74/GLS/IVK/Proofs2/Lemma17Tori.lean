module

public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.IVK.A7.Core

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.PSL2Table CFSG.GH74.GLS.IVK
open scoped MatrixGroups

section FactT

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {p n : ℕ} [hp : Fact p.Prime]

theorem exists_conj_mem_torus
    (hF : Nat.card F = p ^ n) (hp2 : p ≠ 2) (hF2 : ringChar F ≠ 2)
    (hq : 5 ≤ Fintype.card F) {ν : F} (hν : ¬ IsSquare ν) (X : Subgroup PSL(2, F))
    (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X)) (hXcop : Nat.Coprime p (Nat.card X)) :
    (∃ c : PSL(2, F), ∀ x ∈ X, c⁻¹ * x * c ∈ splitTorus F) ∨
      ∃ c : PSL(2, F), ∀ x ∈ X, c⁻¹ * x * c ∈ nonsplitTorus ν := by
  have hcyc : IsCyclic X := by
    rcases odd_subgroup_cases hF hp2 X hX1 hXodd with h | ⟨E, hE1, hEX, hEp, -⟩
    · exact h
    · exfalso
      rcases hEp.card_eq_or_dvd with h1 | h1
      · exact hE1 (Subgroup.card_eq_one.mp h1)
      · have h2 := h1.trans (Subgroup.card_dvd_of_le hEX)
        exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hXcop h2)
  obtain ⟨g, hg⟩ := hcyc
  have hgen : ∀ y ∈ X, ∃ k : ℤ, y = (g : PSL(2, F)) ^ k := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  have hg1 : (g : PSL(2, F)) ≠ 1 := by
    intro h
    apply hX1
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨k, hk⟩ := hgen y hy
    rw [h, one_zpow] at hk
    exact Subgroup.mem_bot.mpr hk
  have hconj : ∀ (T₀ : Subgroup PSL(2, F)) (c : PSL(2, F)),
      c⁻¹ * (g : PSL(2, F)) * c ∈ T₀ → ∀ x ∈ X, c⁻¹ * x * c ∈ T₀ := by
    intro T₀ c hc x hx
    obtain ⟨k, rfl⟩ := hgen x hx
    have : c⁻¹ * (g : PSL(2, F)) ^ k * c = (c⁻¹ * (g : PSL(2, F)) * c) ^ k := by
      have := conj_zpow (a := c⁻¹) (b := (g : PSL(2, F))) (i := k)
      rw [inv_inv] at this
      exact this.symm
    rw [this]
    exact T₀.zpow_mem hc k
  rcases mem_conjSet_cases hF2 hq hν (g : PSL(2, F)) with h | h | ⟨h1, d, hd⟩ | ⟨h1, d, hd⟩
  · exact absurd h hg1
  · exfalso
    have h2 := orderOf_dvd_of_mem_conjSet h
    rw [card_unipotent (Ring.two_ne_zero hF2)] at h2
    have h3 : orderOf (g : PSL(2, F)) ∣ p ^ n := by
      rw [← Nat.card_eq_fintype_card, hF] at h2
      exact h2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp h3
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hg1 hj
    have h4 : p ∣ orderOf (g : PSL(2, F)) := by
      rw [hj]; exact dvd_pow_self p hj0
    have h5 : orderOf (g : PSL(2, F)) ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X g.2
    exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hXcop (h4.trans h5))
  · left
    exact ⟨d⁻¹, hconj _ _ (by rw [inv_inv]; exact hd)⟩
  · right
    exact ⟨d⁻¹, hconj _ _ (by rw [inv_inv]; exact hd)⟩

end FactT

end CFSG.GH74.GLS.IVK.Proofs2

module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Equiv.Perm Subgroup

section Count

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem cycleType_eq_replicate_of_mul_self {σ : Perm α} (hσ : σ * σ = 1) :
    σ.cycleType = Multiset.replicate σ.cycleType.card 2 := by
  rw [Multiset.eq_replicate_card]
  intro m hm
  have h1 : m ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hm
  have h2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hσ)
  have h3 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
  have h4 : m ∣ 2 := h1.trans h2
  exact (Nat.le_of_dvd (by norm_num) h4).antisymm h3

theorem natCard_centralizer_involution {σ : Perm α} (hσ : σ * σ = 1) :
    Nat.card (centralizer ({σ} : Set (Perm α))) =
      (Fintype.card α - 2 * σ.cycleType.card).factorial * 2 ^ σ.cycleType.card *
        σ.cycleType.card.factorial := by
  rw [Equiv.Perm.nat_card_centralizer]
  have hct := cycleType_eq_replicate_of_mul_self hσ
  set k := σ.cycleType.card with hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · have : σ.cycleType = 0 := Multiset.card_eq_zero.1 h0
    rw [this]
    simp [h0]
  · rw [hct]
    simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.prod_replicate, mul_comm 2 k]
    have htf : (Multiset.replicate k 2).toFinset = {2} := by
      rw [Multiset.toFinset_replicate]
      simp [hpos.ne']
    rw [htf, Finset.prod_singleton, Multiset.count_replicate_self]

end Count

section Inequality

theorem factorial_add_two (m : ℕ) :
    (m + 2).factorial = (m + 2) * (m + 1) * m.factorial := by
  rw [Nat.factorial_succ, Nat.factorial_succ]; ring

theorem two_pow_mul_factorial_lt (k : ℕ) (hk : 4 ≤ k) :
    2 ^ k * k.factorial < 2 * (2 * k - 2).factorial := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ m hm ih =>
    have h1 : 2 * (m + 1) - 2 = (2 * m - 2) + 2 := by omega
    rw [h1, factorial_add_two, pow_succ, Nat.factorial_succ]
    have h3 : 2 * (m + 1) ≤ (2 * m - 2 + 2) * (2 * m - 2 + 1) := by
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 4 := ⟨m - 4, by omega⟩
      have : 2 * (t + 4) - 2 = 2 * t + 6 := by omega
      rw [this]; nlinarith
    calc 2 ^ m * 2 * ((m + 1) * m.factorial) = (2 * (m + 1)) * (2 ^ m * m.factorial) := by ring
      _ ≤ ((2 * m - 2 + 2) * (2 * m - 2 + 1)) * (2 ^ m * m.factorial) :=
          Nat.mul_le_mul_right _ h3
      _ < ((2 * m - 2 + 2) * (2 * m - 2 + 1)) * (2 * (2 * m - 2).factorial) :=
          Nat.mul_lt_mul_of_pos_left ih (by positivity)
      _ = 2 * ((2 * m - 2 + 2) * (2 * m - 2 + 1) * (2 * m - 2).factorial) := by ring

theorem cen_lt_two_mul_factorial {N k : ℕ} (hN : 9 ≤ N) (hk : 2 ≤ k) (hkN : 2 * k ≤ N) :
    (N - 2 * k).factorial * 2 ^ k * k.factorial < 2 * (N - 2).factorial := by
  obtain ⟨j, hj⟩ : ∃ j, N = 2 * k + j := ⟨N - 2 * k, by omega⟩
  subst hj
  have hsub : 2 * k + j - 2 * k = j := by omega
  have hsub2 : 2 * k + j - 2 = (2 * k - 2) + j := by omega
  rw [hsub, hsub2]
  have key : (2 * k - 2).factorial * j.factorial ≤ ((2 * k - 2) + j).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  rcases (by omega : k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | h4
  ·
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 5 := ⟨j - 5, by omega⟩
    have h1 : 2 * 2 - 2 + (i + 5) = (i + 5) + 2 := by omega
    rw [h1, factorial_add_two (i + 5)]
    have hpos := Nat.factorial_pos (i + 5)
    generalize (i + 5).factorial = F at hpos ⊢
    have h2 : 4 * F < (i + 5 + 2) * (i + 5 + 1) * F :=
      Nat.mul_lt_mul_of_pos_right (by nlinarith) hpos
    have h3 : Nat.factorial 2 = 2 := rfl
    rw [h3]
    nlinarith
  ·
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
    have h1 : 2 * 3 - 2 + (i + 3) = (i + 3 + 2) + 2 := by omega
    rw [h1, factorial_add_two (i + 3 + 2), factorial_add_two (i + 3)]
    have hpos := Nat.factorial_pos (i + 3)
    generalize (i + 3).factorial = F at hpos ⊢
    have h2 : 24 < (i + 3 + 2 + 2) * (i + 3 + 2 + 1) * ((i + 3 + 2) * (i + 3 + 1)) := by
      have hA : 7 * 6 ≤ (i + 3 + 2 + 2) * (i + 3 + 2 + 1) :=
        Nat.mul_le_mul (show 7 ≤ i + 3 + 2 + 2 by omega) (show 6 ≤ i + 3 + 2 + 1 by omega)
      have hB : 5 * 4 ≤ (i + 3 + 2) * (i + 3 + 1) :=
        Nat.mul_le_mul (show 5 ≤ i + 3 + 2 by omega) (show 4 ≤ i + 3 + 1 by omega)
      have := Nat.mul_le_mul hA hB
      omega
    have h3 : 24 * F < (i + 3 + 2 + 2) * (i + 3 + 2 + 1) * ((i + 3 + 2) * (i + 3 + 1)) * F :=
      Nat.mul_lt_mul_of_pos_right h2 hpos
    have h4 : Nat.factorial 3 = 6 := rfl
    rw [h4]
    nlinarith
  · have hmain := two_pow_mul_factorial_lt k h4
    calc j.factorial * 2 ^ k * k.factorial = j.factorial * (2 ^ k * k.factorial) := by ring
      _ < j.factorial * (2 * (2 * k - 2).factorial) :=
          Nat.mul_lt_mul_of_pos_left hmain (Nat.factorial_pos _)
      _ = 2 * ((2 * k - 2).factorial * j.factorial) := by ring
      _ ≤ 2 * ((2 * k - 2) + j).factorial := Nat.mul_le_mul_left 2 key

end Inequality

section Swap

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem isSwap_of_natCard_centralizer {σ : Perm α} (hN : 7 ≤ Fintype.card α) (hσ : σ * σ = 1)
    (hc : Nat.card (centralizer ({σ} : Set (Perm α))) = 2 * (Fintype.card α - 2).factorial) :
    σ.IsSwap := by
  rw [natCard_centralizer_involution hσ] at hc
  set k := σ.cycleType.card with hk
  have hsupp : σ.support.card = 2 * k := by
    have := Equiv.Perm.sum_cycleType σ
    rw [cycleType_eq_replicate_of_mul_self hσ] at this
    simpa [Multiset.sum_replicate, mul_comm] using this.symm
  have hkN : 2 * k ≤ Fintype.card α := by
    rw [← hsupp]; exact Finset.card_le_univ _
  rcases Nat.lt_or_ge k 2 with hlt | hge
  · interval_cases k
    ·
      exfalso
      simp only [mul_zero, Nat.sub_zero, pow_zero, Nat.factorial_zero, mul_one] at hc
      have h2 : (Fintype.card α).factorial = 2 * (Fintype.card α - 2).factorial := hc
      obtain ⟨m, hm⟩ : ∃ m, Fintype.card α = m + 2 := ⟨Fintype.card α - 2, by omega⟩
      have hm7 : 5 ≤ m := by omega
      rw [hm] at h2
      simp only [Nat.add_sub_cancel] at h2
      rw [Nat.factorial_succ, Nat.factorial_succ] at h2
      have hpos := Nat.factorial_pos m
      have h3 : ((m + 1 + 1) * (m + 1)) * m.factorial = 2 * m.factorial := by rw [← h2]; ring
      have h4 := Nat.eq_of_mul_eq_mul_right hpos h3
      nlinarith
    ·
      rw [Equiv.Perm.isSwap_iff_cycleType]
      have := cycleType_eq_replicate_of_mul_self hσ
      rw [← hk] at this
      simpa using this
  · exfalso
    rcases (by omega : Fintype.card α = 7 ∨ Fintype.card α = 8 ∨ 9 ≤ Fintype.card α) with
      h7 | h8 | h9
    · rw [h7] at hc hkN
      have hk3 : k ≤ 3 := by omega
      interval_cases k <;> revert hc <;> decide
    · rw [h8] at hc hkN
      have hk4 : k ≤ 4 := by omega
      interval_cases k <;> revert hc <;> decide
    · have := cen_lt_two_mul_factorial h9 hge hkN
      omega

theorem natCard_centralizer_map {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (x : X) :
    Nat.card (centralizer ({φ x} : Set Y)) = Nat.card (centralizer ({x} : Set X)) := by
  have h : centralizer ({φ x} : Set Y) = (centralizer ({x} : Set X)).map φ.toMonoidHom := by
    ext y
    rw [mem_centralizer_singleton_iff, Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      rw [mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨w, hw, rfl⟩
      rw [mem_centralizer_singleton_iff] at hw
      show φ w * φ x = φ x * φ w
      rw [← map_mul, ← map_mul, hw]
  rw [h]
  exact Nat.card_congr ((centralizer ({x} : Set X)).equivMapOfInjective φ.toMonoidHom
    φ.injective).symm.toEquiv

theorem isSwap_map_of_mulEquiv {β : Type*} [Fintype β] [DecidableEq β]
    (φ : Perm α ≃* Perm β) (hcard : Fintype.card α = Fintype.card β) (hN : 7 ≤ Fintype.card α)
    {τ : Perm α} (hτ : τ.IsSwap) : (φ τ).IsSwap := by
  have hτ2 : τ * τ = 1 := by
    obtain ⟨x, y, hxy, rfl⟩ := hτ
    exact swap_mul_self x y
  have hφ2 : φ τ * φ τ = 1 := by rw [← map_mul, hτ2, map_one]
  have hcτ : Nat.card (centralizer ({τ} : Set (Perm α))) = 2 * (Fintype.card α - 2).factorial := by
    rw [natCard_centralizer_involution hτ2]
    have hct : τ.cycleType = {2} := Equiv.Perm.isSwap_iff_cycleType.1 hτ
    rw [hct]
    simp only [Multiset.card_singleton, mul_one, pow_one, Nat.factorial_one]
    ring
  apply isSwap_of_natCard_centralizer (hcard ▸ hN) hφ2
  rw [natCard_centralizer_map φ τ, hcτ, hcard]

end Swap

end CFSG.OddStandard.AltStdSec

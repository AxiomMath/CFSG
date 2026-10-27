module

public import CFSG.CharacterTheory.Burnside
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup

variable {P : Type*} [Group P]

private lemma sixty_divisors (k : ℕ) (hk : k ∣ 60) :
    k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 10 ∨ k = 12 ∨
      k = 15 ∨ k = 20 ∨ k = 30 ∨ k = 60 := by
  have hk60 : k ≤ 60 := Nat.le_of_dvd (by norm_num) hk
  have hk1 : 1 ≤ k := Nat.pos_of_dvd_of_pos hk (by norm_num)
  interval_cases k using hk1, hk60
  all_goals norm_num at hk
  all_goals norm_num

private lemma isSolvable_of_card_eq_prime_pow_mul_prime_pow_subgroup [Finite P]
    {Q : Subgroup P} {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hcard : Nat.card Q = p ^ a * q ^ b) :
    Group.IsSolvable ↥Q := by
  haveI : Fintype ↥Q := Fintype.ofFinite ↥Q
  refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (G := ↥Q) (a := a) (b := b) hp hq hpq ?_
  simpa only [Nat.card_eq_fintype_card] using hcard

private lemma false_of_perfect_of_card_eq_prime_pow_mul_prime_pow [Finite P]
    {Q : Subgroup P} {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hcard : Nat.card Q = p ^ a * q ^ b)
    (hperf : ⁅Q, Q⁆ = Q) (hne : Q ≠ ⊥) : False := by
  haveI : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.mpr hperf
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  exact Group.IsPerfect.not_isSolvable ↥Q
    (isSolvable_of_card_eq_prime_pow_mul_prime_pow_subgroup hp hq hpq hcard)

private lemma false_of_perfect_of_card_eq_factor [Finite P]
    {Q : Subgroup P} {k p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hk1 : k ≠ 1) (hcard : Nat.card Q = k) (hfac : k = p ^ a * q ^ b)
    (hperf : ⁅Q, Q⁆ = Q) : False := by
  have hcard' : Nat.card Q = p ^ a * q ^ b := by rw [hcard, hfac]
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact hk1 hcard.symm
  exact false_of_perfect_of_card_eq_prime_pow_mul_prime_pow hp hq hpq hcard' hperf hQne

theorem eq_bot_or_eq_of_perfect_of_card_sixty [Finite P] {J : Subgroup P}
    (hJ : Nat.card ↥J = 60) (hsq : ∀ Q : Subgroup P, (∀ g ∈ J, g * g ∈ Q) → J ≤ Q) :
    ∀ Q ≤ J, ⁅Q, Q⁆ = Q → Q = ⊥ ∨ Q = J := by
  classical
  intro Q hQJ hQperf
  have hdvd : Nat.card Q ∣ 60 := by
    rw [← hJ]
    exact Subgroup.card_dvd_of_le hQJ
  rcases sixty_divisors (Nat.card Q) hdvd with
    h1 | h2 | h3 | h4 | h5 | h6 | h10 | h12 | h15 | h20 | h30 | h60
  · left
    exact Subgroup.eq_bot_of_card_eq Q h1
  · exfalso
    exact false_of_perfect_of_card_eq_factor (Q := Q) (k := 2)
      Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) h2
      (by norm_num : (2 : ℕ) = 2 ^ 1 * 3 ^ 0) hQperf
  · exfalso
    exact false_of_perfect_of_card_eq_factor (Q := Q) (k := 3)
      Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) h3
      (by norm_num : (3 : ℕ) = 2 ^ 0 * 3 ^ 1) hQperf
  · exfalso
    exact false_of_perfect_of_card_eq_factor (Q := Q) (k := 4)
      Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) h4
      (by norm_num : (4 : ℕ) = 2 ^ 2 * 3 ^ 0) hQperf
  · exfalso
    exact false_of_perfect_of_card_eq_factor (Q := Q) (k := 5)
      Nat.prime_five Nat.prime_two (by norm_num) (by norm_num) h5
      (by norm_num : (5 : ℕ) = 5 ^ 1 * 2 ^ 0) hQperf
  · exfalso
    exact false_of_perfect_of_card_eq_factor (Q := Q) (k := 6)
      Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) h6
      (by norm_num : (6 : ℕ) = 2 ^ 1 * 3 ^ 1) hQperf
  · exfalso
    exact false_of_perfect_of_card_eq_factor (Q := Q) (k := 10)
      Nat.prime_two Nat.prime_five (by norm_num) (by norm_num) h10
      (by norm_num : (10 : ℕ) = 2 ^ 1 * 5 ^ 1) hQperf
  · exfalso
    exact false_of_perfect_of_card_eq_factor (Q := Q) (k := 12)
      Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) h12
      (by norm_num : (12 : ℕ) = 2 ^ 2 * 3 ^ 1) hQperf
  · exfalso
    exact false_of_perfect_of_card_eq_factor (Q := Q) (k := 15)
      Nat.prime_three Nat.prime_five (by norm_num) (by norm_num) h15
      (by norm_num : (15 : ℕ) = 3 ^ 1 * 5 ^ 1) hQperf
  · exfalso
    exact false_of_perfect_of_card_eq_factor (Q := Q) (k := 20)
      Nat.prime_two Nat.prime_five (by norm_num) (by norm_num) h20
      (by norm_num : (20 : ℕ) = 2 ^ 2 * 5 ^ 1) hQperf
  ·
    let Q' : Subgroup ↥J := Q.subgroupOf J
    have hQ'card : Nat.card Q' = 30 := by
      change Nat.card (Q.subgroupOf J) = 30
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQJ).toEquiv, h30]
    have hindex : Q'.index = 2 := by
      have h := Subgroup.card_mul_index Q'
      rw [hQ'card, hJ] at h
      omega
    have hJQ : J ≤ Q := by
      apply hsq Q
      intro g hg
      have hmem : (⟨g, hg⟩ : ↥J) * ⟨g, hg⟩ ∈ Q' :=
        Subgroup.mul_self_mem_of_index_two hindex ⟨g, hg⟩
      rwa [Subgroup.mem_subgroupOf] at hmem
    have hcardle : Nat.card J ≤ Nat.card Q := Subgroup.card_le_of_le hJQ
    rw [hJ, h30] at hcardle
    omega
  · right
    exact Subgroup.eq_of_le_of_card_ge hQJ (by omega)

end CFSG.EvenSporadicStandard.M12Std.Rbc

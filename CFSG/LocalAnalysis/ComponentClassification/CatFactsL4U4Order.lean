module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

theorem exists_odd_prime_dvd_sq_add_one {q : ℕ} (hq : Odd q) (h3 : 3 ≤ q) :
    ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ∣ q ^ 2 + 1 := by
  obtain ⟨t, rfl⟩ := hq
  set m := 2 * t ^ 2 + 2 * t + 1 with hm
  have hm1 : m ≠ 1 := by
    have : 1 ≤ t := by omega
    nlinarith
  refine ⟨m.minFac, Nat.minFac_prime hm1, ?_, ?_⟩
  · intro h2
    have h := Nat.minFac_dvd m
    rw [h2] at h
    omega
  · refine (Nat.minFac_dvd m).trans ⟨2, ?_⟩
    rw [hm]
    ring

theorem not_dvd_pow_sub_one {q s e : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hq : 1 ≤ q)
    (hsq : s ∣ q ^ 2 ^ e + 1) {j : ℕ} (hj : 1 ≤ j) (hje : j < 2 ^ (e + 1)) :
    ¬ s ∣ q ^ j - 1 := by
  have := Fact.mk hs
  intro hdiv
  have hx : ((q : ZMod s)) ^ 2 ^ e = -1 := by
    have h := (ZMod.natCast_eq_zero_iff _ s).2 hsq
    push_cast at h
    linear_combination h
  have hne : ((q : ZMod s)) ^ 2 ^ e ≠ 1 := by
    rw [hx]
    intro h
    have h2 : (2 : ZMod s) = 0 := by linear_combination -h
    have : s ∣ 2 := by exact_mod_cast (ZMod.natCast_eq_zero_iff 2 s).1 (by exact_mod_cast h2)
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).1 this)
  have hfin : ((q : ZMod s)) ^ 2 ^ (e + 1) = 1 := by
    rw [pow_succ, pow_mul, hx]
    norm_num
  have hord : orderOf (q : ZMod s) = 2 ^ (e + 1) :=
    orderOf_eq_prime_pow (p := 2) (hp := ⟨Nat.prime_two⟩) hne hfin
  have hj1 : ((q : ZMod s)) ^ j = 1 := by
    have h := (ZMod.natCast_eq_zero_iff _ s).2 hdiv
    have hqj : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq
    rw [Nat.cast_sub hqj] at h
    push_cast at h
    linear_combination h
  have := orderOf_dvd_of_pow_eq_one hj1
  rw [hord] at this
  exact absurd (Nat.le_of_dvd (by omega) this) (by omega)

theorem not_dvd_of_dvd_pow_add_one {q s e : ℕ} (hs : s.Prime) (hsq : s ∣ q ^ 2 ^ e + 1) :
    ¬ s ∣ q := by
  intro h
  have h1 : s ∣ q ^ 2 ^ e := dvd_pow h (by positivity)
  have : s ∣ 1 := (Nat.dvd_add_right h1).1 hsq
  exact hs.one_lt.ne' (Nat.dvd_one.1 this)

theorem not_dvd_card_GL {F : Type*} [Field F] [Fintype F] {s e : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsq : s ∣ (Fintype.card F) ^ 2 ^ e + 1) {d : ℕ} (hd : d < 2 ^ (e + 1)) :
    ¬ s ∣ Nat.card (GL (Fin d) F) := by
  set q := Fintype.card F with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  rw [Matrix.card_GL_field (𝔽 := F) d]
  intro hdiv
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hs.prime _).1 hdiv
  have hid : (i : ℕ) < d := i.2
  have hfac : q ^ d - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (d - i) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hid.le]
  rw [hfac] at hi
  rcases (Nat.Prime.dvd_mul hs).1 hi with h | h
  · exact not_dvd_of_dvd_pow_add_one hs hsq (hs.dvd_of_dvd_pow h)
  · exact not_dvd_pow_sub_one hs hs2 hq1 hsq (by omega) (by omega) h

theorem eq_one_of_pow_eq_one_of_not_dvd {G : Type*} [Group G] [Finite G] {s : ℕ} (hs : s.Prime)
    (hcard : ¬ s ∣ Nat.card G) {g : G} (hg : g ^ s = 1) : g = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one hg
  rcases (Nat.dvd_prime hs).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ orderOf_dvd_natCard g) hcard

end CFSG.ComponentClassification.CatFactsL4U4

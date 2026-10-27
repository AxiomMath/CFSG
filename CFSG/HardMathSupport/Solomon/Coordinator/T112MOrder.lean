module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem t112m_factorization_eq_three {n m : ℕ} (h : n = 3 ^ 3 * m) (hm : ¬ 3 ∣ m) :
    n.factorization 3 = 3 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  subst h
  rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd hm]
  rfl

theorem t112m_not_dvd_three_mul_add_one (a : ℕ) : ¬ 3 ∣ 3 * a + 1 := by omega

theorem t112m_factorization_SL {q : ℕ} (hq : q % 9 = 4 ∨ q % 9 = 7) :
    (q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1)).factorization 3 = 3 := by
  obtain ⟨s, rfl⟩ : ∃ s, q = 3 * s + 1 := ⟨q / 3, by omega⟩
  have hs : ¬ 3 ∣ s := by omega
  have h1 : (3 * s + 1) ^ 3 - 1 = 9 * s * (3 * (s ^ 2 + s) + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have h2 : (3 * s + 1) ^ 2 - 1 = 3 * s * (3 * s + 2) := by
    apply Nat.sub_eq_of_eq_add
    ring
  refine t112m_factorization_eq_three
    (m := (3 * s + 1) ^ 3 * s ^ 2 * (3 * (s ^ 2 + s) + 1) * (3 * s + 2)) ?_ ?_
  · rw [h1, h2]
    ring
  · have hp := Nat.prime_three
    intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
        · exact t112m_not_dvd_three_mul_add_one s (hp.dvd_of_dvd_pow hd)
        · exact hs (hp.dvd_of_dvd_pow hd)
      · exact t112m_not_dvd_three_mul_add_one _ hd
    · omega

theorem t112m_factorization_SU {q : ℕ} (hq : q % 9 = 2 ∨ q % 9 = 5) :
    (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)).factorization 3 = 3 := by
  obtain ⟨s, rfl⟩ : ∃ s, q = 3 * s + 2 := ⟨q / 3, by omega⟩
  have hs : ¬ 3 ∣ s + 1 := by omega
  have h2 : (3 * s + 2) ^ 2 - 1 = 3 * (3 * s + 1) * (s + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  refine t112m_factorization_eq_three
    (m := (3 * s + 2) ^ 3 * (3 * s + 1) * (s + 1) ^ 2 * (3 * (s ^ 2 + s) + 1)) ?_ ?_
  · rw [h2]
    ring
  · have hp := Nat.prime_three
    intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
        · have := hp.dvd_of_dvd_pow hd
          omega
        · exact t112m_not_dvd_three_mul_add_one s hd
      · exact hs (hp.dvd_of_dvd_pow hd)
    · exact t112m_not_dvd_three_mul_add_one _ hd

end CFSG.HardMathSupport.Solomon.Coordinator

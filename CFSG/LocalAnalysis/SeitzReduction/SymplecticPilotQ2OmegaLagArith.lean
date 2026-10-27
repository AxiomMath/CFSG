module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.SeitzReduction.SymplecticPilot

section Arith

theorem not_three_dvd_two_pow_odd_sub_one (a : ℕ) : ¬ 3 ∣ 2 ^ (2 * a + 1) - 1 := by
  have h4 : 4 ^ a % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, show (2 : ℕ) ^ 2 = 4 by norm_num, h4]
  rw [Nat.dvd_iff_mod_eq_zero]
  generalize 2 ^ (2 * a + 1) = x at h2 ⊢
  omega

theorem three_dvd_two_pow_even_sub_one (j : ℕ) : 3 ∣ 2 ^ (2 * j) - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow 4 1 j
  rw [one_pow] at h
  rwa [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]

abbrev lagThreeVal (j : ℕ) : ℕ := (2 ^ j - 1).factorization 3

theorem factorization_three_two_pow_sub_two_pow {d i : ℕ} (hi : i < d) :
    (2 ^ d - 2 ^ i).factorization 3 = lagThreeVal (d - i) := by
  have hfac : 2 ^ d - 2 ^ i = 2 ^ i * (2 ^ (d - i) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hi.le]
  have h1 : 1 < 2 ^ (d - i) := Nat.one_lt_two_pow (by omega)
  rw [hfac, Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization Nat.prime_two,
    Finsupp.single_eq_of_ne (by norm_num), smul_zero, zero_add]

theorem factorization_three_prod_two_pow_sub_two_pow (d : ℕ) :
    (∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ))).factorization 3 =
      ∑ j ∈ Finset.range d, lagThreeVal (j + 1) := by
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin d)), 2 ^ d - 2 ^ (i : ℕ) ≠ 0 := by
    intro i _
    have : 2 ^ (i : ℕ) < 2 ^ d := Nat.pow_lt_pow_right (by norm_num) i.2
    omega
  rw [Nat.factorization_prod hne, Finset.sum_apply']
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    factorization_three_two_pow_sub_two_pow i.2]
  rw [Fin.sum_univ_eq_sum_range (fun i => lagThreeVal (d - i)) d,
    ← Finset.sum_range_reflect (fun j => lagThreeVal (j + 1)) d]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  congr 1
  omega

theorem sum_lagThreeVal_odd (a : ℕ) :
    ∑ j ∈ Finset.range (2 * a + 1), lagThreeVal (j + 1) =
      ∑ j ∈ Finset.range a, lagThreeVal (2 * (j + 1)) := by
  induction a with
  | zero => simp [lagThreeVal]
  | succ a ih =>
    rw [show 2 * (a + 1) + 1 = 2 * a + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have h0 : lagThreeVal (2 * a + 1 + 1 + 1) = 0 := by
      rw [lagThreeVal, show 2 * a + 1 + 1 + 1 = 2 * (a + 1) + 1 by ring]
      exact Nat.factorization_eq_zero_of_not_dvd (not_three_dvd_two_pow_odd_sub_one _)
    rw [h0, add_zero, show 2 * a + 1 + 1 = 2 * (a + 1) by ring]

theorem sum_Icc_lagThreeVal (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, (2 ^ (2 * j) - 1).factorization 3 =
      ∑ j ∈ Finset.range m, lagThreeVal (2 * (j + 1)) := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

theorem factorization_three_card_sp_two (m : ℕ) :
    (2 ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (2 ^ (2 * j) - 1)).factorization 3 =
      ∑ j ∈ Finset.range m, lagThreeVal (2 * (j + 1)) := by
  have hne : ∀ j ∈ Finset.Icc 1 m, 2 ^ (2 * j) - 1 ≠ 0 := by
    intro j hj
    have : 1 < 2 ^ (2 * j) := Nat.one_lt_two_pow (by rw [Finset.mem_Icc] at hj; omega)
    omega
  have hprod : ∏ j ∈ Finset.Icc 1 m, (2 ^ (2 * j) - 1) ≠ 0 := Finset.prod_ne_zero_iff.2 hne
  rw [Nat.factorization_mul (by positivity) hprod, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization Nat.prime_two,
    Finsupp.single_eq_of_ne (by norm_num), smul_zero, zero_add, Nat.factorization_prod hne,
    Finset.sum_apply', sum_Icc_lagThreeVal]

theorem not_dvd_prod_two_pow_sub_two_pow {m d : ℕ} (hm : 1 ≤ m) (hd : d + 1 ≤ 2 * m) :
    ¬ (2 ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (2 ^ (2 * j) - 1)) ∣
      ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  intro h
  have hne : ∀ j ∈ Finset.Icc 1 m, 2 ^ (2 * j) - 1 ≠ 0 := by
    intro j hj
    have : 1 < 2 ^ (2 * j) := Nat.one_lt_two_pow (by rw [Finset.mem_Icc] at hj; omega)
    omega
  have hS : 2 ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (2 ^ (2 * j) - 1) ≠ 0 :=
    mul_ne_zero (by positivity) (Finset.prod_ne_zero_iff.2 hne)
  have hG : ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    have : 2 ^ (i : ℕ) < 2 ^ d := Nat.pow_lt_pow_right (by norm_num) i.2
    omega
  have hle := (Nat.factorization_le_iff_dvd hS hG).2 h 3
  rw [factorization_three_card_sp_two, factorization_three_prod_two_pow_sub_two_pow] at hle
  have hsub : ∑ j ∈ Finset.range d, lagThreeVal (j + 1) ≤
      ∑ j ∈ Finset.range (2 * (m - 1) + 1), lagThreeVal (j + 1) :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
  rw [sum_lagThreeVal_odd] at hsub
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ] at hle
  rw [Nat.add_sub_cancel] at hsub
  have hpos : 0 < lagThreeVal (2 * (k + 1)) := by
    have h1 : 1 < 2 ^ (2 * (k + 1)) := Nat.one_lt_two_pow (by omega)
    exact Nat.Prime.factorization_pos_of_dvd Nat.prime_three (by omega)
      (three_dvd_two_pow_even_sub_one _)
  omega

end Arith

theorem eq_one_of_isSimpleGroup_of_not_dvd {X Y : Type*} [Group X] [IsSimpleGroup X] [Group Y]
    (f : X →* Y) (h : ¬ Nat.card X ∣ Nat.card Y) (x : X) : f x = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hk | hk
  · exact absurd (Subgroup.card_dvd_of_injective f ((MonoidHom.ker_eq_bot_iff f).1 hk)) h
  · exact MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top x)

end CFSG.SeitzReduction.SymplecticPilot

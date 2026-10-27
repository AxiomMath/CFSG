module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOrd
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

@[expose] def u42ProdSq (q m : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 m, (q ^ (2 * j) - 1)

@[expose] def u42Sp (q m : ℕ) : ℕ := q ^ (m ^ 2) * u42ProdSq q m

@[expose] def u42OEvenPlus (q m : ℕ) : ℕ :=
  2 * q ^ (m * (m + 1)) * (q ^ (m + 1) - 1) * u42ProdSq q m

@[expose] def u42OEvenMinus (q m : ℕ) : ℕ :=
  2 * q ^ (m * (m + 1)) * (q ^ (m + 1) + 1) * u42ProdSq q m

theorem u42ProdSq_ne_zero {f : ℕ} (hf : 1 ≤ f) (m : ℕ) : u42ProdSq (3 ^ f) m ≠ 0 := by
  unfold u42ProdSq
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hlt : 1 < (3 ^ f) ^ (2 * j) :=
    Nat.one_lt_pow (by omega) (Nat.one_lt_pow (by omega) (by norm_num))
  omega

theorem u42_factorization_three_u42ProdSq {f : ℕ} (hf : 1 ≤ f) (m : ℕ) :
    (u42ProdSq (3 ^ f) m).factorization 3 = 0 := by
  unfold u42ProdSq
  have hne : ∀ j ∈ Finset.Icc 1 m, (3 ^ f) ^ (2 * j) - 1 ≠ 0 := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hlt : 1 < (3 ^ f) ^ (2 * j) :=
      Nat.one_lt_pow (by omega) (Nat.one_lt_pow (by omega) (by norm_num))
    omega
  rw [Nat.factorization_prod hne, Finsupp.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  exact Nat.factorization_eq_zero_of_not_dvd (u42_not_three_dvd_pow_sub_one hf (by omega))

theorem u42_factorization_three_u42Sp {f : ℕ} (hf : 1 ≤ f) (m : ℕ) :
    (u42Sp (3 ^ f) m).factorization 3 = f * m ^ 2 := by
  unfold u42Sp
  rw [Nat.factorization_mul (by positivity) (u42ProdSq_ne_zero hf m), Finsupp.add_apply,
    u42_factorization_three_u42ProdSq hf m, add_zero, ← pow_mul,
    Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem u42_factorization_three_u42OEvenPlus {f : ℕ} (hf : 1 ≤ f) (m : ℕ) :
    (u42OEvenPlus (3 ^ f) m).factorization 3 = f * (m * (m + 1)) := by
  unfold u42OEvenPlus
  have hlt : 1 < (3 ^ f) ^ (m + 1) :=
    Nat.one_lt_pow (by omega) (Nat.one_lt_pow (by omega) (by norm_num))
  have hne1 : (3 ^ f) ^ (m + 1) - 1 ≠ 0 := by omega
  rw [Nat.factorization_mul (mul_ne_zero (by positivity) hne1) (u42ProdSq_ne_zero hf m),
    Nat.factorization_mul (by positivity) hne1, Finsupp.add_apply, Finsupp.add_apply,
    u42_factorization_three_u42ProdSq hf m,
    Nat.factorization_eq_zero_of_not_dvd (u42_not_three_dvd_pow_sub_one hf (by omega)),
    Nat.factorization_mul (by norm_num) (by positivity)]
  rw [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2),
    ← pow_mul, Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem u42_factorization_three_u42OEvenMinus {f : ℕ} (hf : 1 ≤ f) (m : ℕ) :
    (u42OEvenMinus (3 ^ f) m).factorization 3 = f * (m * (m + 1)) := by
  unfold u42OEvenMinus
  have hne1 : (3 ^ f) ^ (m + 1) + 1 ≠ 0 := by omega
  rw [Nat.factorization_mul (mul_ne_zero (by positivity) hne1) (u42ProdSq_ne_zero hf m),
    Nat.factorization_mul (by positivity) hne1, Finsupp.add_apply, Finsupp.add_apply,
    u42_factorization_three_u42ProdSq hf m,
    Nat.factorization_eq_zero_of_not_dvd (u42_not_three_dvd_pow_add_one hf (by omega)),
    Nat.factorization_mul (by norm_num) (by positivity)]
  rw [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2),
    ← pow_mul, Nat.Prime.factorization_pow Nat.prime_three]
  simp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

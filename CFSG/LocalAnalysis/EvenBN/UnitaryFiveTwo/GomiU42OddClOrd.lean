module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClV3

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

@[expose] def u42GL (q k : ℕ) : ℕ := ∏ i ∈ Finset.range k, (q ^ k - q ^ i)

@[expose] def u42GU (q k : ℕ) : ℕ :=
  q ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 1 k, (if i % 2 = 1 then q ^ i + 1 else q ^ i - 1)

theorem u42_factorization_three_u42GL {f : ℕ} (hf : 1 ≤ f) (k : ℕ) :
    (u42GL (3 ^ f) k).factorization 3 = f * (k * (k - 1) / 2) := by
  unfold u42GL
  rw [← Fin.prod_univ_eq_prod_range (fun i => (3 ^ f) ^ k - (3 ^ f) ^ i) k]
  exact u42_factorization_three_prod_GL hf k

theorem u42_not_three_dvd_pow_add_one {f i : ℕ} (hf : 1 ≤ f) (hi : 1 ≤ i) :
    ¬ 3 ∣ (3 ^ f) ^ i + 1 := by
  intro h
  have h1 : 3 ∣ (3 ^ f) ^ i := dvd_pow (dvd_pow_self 3 (by omega)) (by omega)
  have h2 := (Nat.dvd_add_right h1).mp h
  omega

theorem u42_not_three_dvd_pow_sub_one {f i : ℕ} (hf : 1 ≤ f) (hi : 1 ≤ i) :
    ¬ 3 ∣ (3 ^ f) ^ i - 1 := by
  intro h
  have h1 : 3 ∣ (3 ^ f) ^ i := dvd_pow (dvd_pow_self 3 (by omega)) (by omega)
  have hpos : 1 ≤ (3 ^ f) ^ i := Nat.one_le_pow _ _ (by positivity)
  have h2 : 3 ∣ (3 ^ f) ^ i - ((3 ^ f) ^ i - 1) := Nat.dvd_sub h1 h
  have h3 : (3 ^ f) ^ i - ((3 ^ f) ^ i - 1) = 1 := by omega
  rw [h3] at h2
  omega

theorem u42_factorization_three_u42GU {f : ℕ} (hf : 1 ≤ f) (k : ℕ) :
    (u42GU (3 ^ f) k).factorization 3 = f * (k * (k - 1) / 2) := by
  unfold u42GU
  have hne : ∀ i ∈ Finset.Icc 1 k,
      (if i % 2 = 1 then (3 ^ f) ^ i + 1 else (3 ^ f) ^ i - 1) ≠ 0 := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hlt : 1 < (3 ^ f) ^ i := Nat.one_lt_pow (by omega) (Nat.one_lt_pow (by omega) (by norm_num))
    split_ifs <;> omega
  rw [Nat.factorization_mul (by positivity) (Finset.prod_ne_zero_iff.mpr hne), Finsupp.add_apply,
    Nat.factorization_prod hne]
  have hprod : (∑ i ∈ Finset.Icc 1 k,
      (if i % 2 = 1 then (3 ^ f) ^ i + 1 else (3 ^ f) ^ i - 1).factorization) 3 = 0 := by
    rw [Finsupp.coe_finset_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    apply Nat.factorization_eq_zero_of_not_dvd
    split_ifs
    · exact u42_not_three_dvd_pow_add_one hf hi1
    · exact u42_not_three_dvd_pow_sub_one hf hi1
  rw [hprod, add_zero, ← pow_mul, Nat.Prime.factorization_pow Nat.prime_three]
  simp [mul_comm]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

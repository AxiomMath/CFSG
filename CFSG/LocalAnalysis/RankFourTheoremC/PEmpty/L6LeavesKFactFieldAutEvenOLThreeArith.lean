module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

namespace OLThreeAdic

theorem two_pow_mod_nine (n : ℕ) : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem prime_mod_six {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    rcases hp.eq_one_or_self_of_dvd 2 h with h | h <;> omega
  have h3 : ¬ 3 ∣ p := fun h => by
    rcases hp.eq_one_or_self_of_dvd 3 h with h | h <;> omega
  omega

theorem padicValNat_three_sub_one_zero {X : ℕ} (hX : 1 ≤ X)
    (h : X % 9 = 2 ∨ X % 9 = 5 ∨ X % 9 = 8) : padicValNat 3 (X - 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  omega

theorem padicValNat_three_sub_one_one {X : ℕ} (hX : 1 ≤ X) (h : X % 9 = 4 ∨ X % 9 = 7) :
    padicValNat 3 (X - 1) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : X - 1 ≠ 0 := by omega
  have h1 : 1 ≤ padicValNat 3 (X - 1) :=
    (padicValNat_dvd_iff_le hne).mp (by rw [pow_one]; omega)
  have h2 : ¬ 2 ≤ padicValNat 3 (X - 1) := fun h2 => by
    have := (padicValNat_dvd_iff_le hne).mpr h2
    omega
  omega

theorem two_pow_mod_nine_odd {n : ℕ} (h : n % 2 = 1) :
    2 ^ n % 9 = 2 ∨ 2 ^ n % 9 = 5 ∨ 2 ^ n % 9 = 8 := by
  rw [two_pow_mod_nine]
  have key : ∀ r : Fin 6, r.val % 2 = 1 →
      2 ^ r.val % 9 = 2 ∨ 2 ^ r.val % 9 = 5 ∨ 2 ^ r.val % 9 = 8 := by decide
  exact key ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩ (by simp only; omega)

theorem two_pow_mod_nine_even {n : ℕ} (h : n % 6 = 2 ∨ n % 6 = 4) :
    2 ^ n % 9 = 4 ∨ 2 ^ n % 9 = 7 := by
  rw [two_pow_mod_nine]
  have key : ∀ r : Fin 6, r.val = 2 ∨ r.val = 4 → 2 ^ r.val % 9 = 4 ∨ 2 ^ r.val % 9 = 7 := by
    decide
  exact key ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩ (by simp only; omega)

theorem padicValNat_three_two_pow_mul_sub_one {p k : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) (hk1 : 1 ≤ k)
    (hk5 : k ≤ 5) : padicValNat 3 (2 ^ (p * k) - 1) = (k + 1) % 2 := by
  have hpos : 1 ≤ 2 ^ (p * k) := Nat.one_le_two_pow
  interval_cases k
  · exact padicValNat_three_sub_one_zero hpos (two_pow_mod_nine_odd (by omega))
  · exact padicValNat_three_sub_one_one hpos (two_pow_mod_nine_even (by omega))
  · exact padicValNat_three_sub_one_zero hpos (two_pow_mod_nine_odd (by omega))
  · exact padicValNat_three_sub_one_one hpos (two_pow_mod_nine_even (by omega))
  · exact padicValNat_three_sub_one_zero hpos (two_pow_mod_nine_odd (by omega))

theorem padicValNat_three_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat 3 (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat 3 (f i) := by
  have h := Nat.factorization_prod hf
  rw [← Nat.factorization_def _ Nat.prime_three, h, Finsupp.finset_sum_apply]
  exact Finset.sum_congr rfl fun i _ => Nat.factorization_def _ Nat.prime_three

theorem not_three_dvd_two_pow (m : ℕ) : ¬ 3 ∣ 2 ^ m := fun h => by
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem two_le_two_pow_mul {p m : ℕ} (hp : 1 ≤ p) (hm : 1 ≤ m) : 2 ≤ 2 ^ (p * m) :=
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (p * m) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_pos hp hm)

theorem padicValNat_three_prod_gl {p : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) {a : ℕ} (ha : a ≤ 5) :
    padicValNat 3 (∏ i : Fin a, ((2 ^ p) ^ a - (2 ^ p) ^ (i : ℕ))) = a / 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : 1 ≤ p := by omega
  have hfac : ∀ i : Fin a, (2 ^ p) ^ a - (2 ^ p) ^ (i : ℕ) =
      2 ^ (p * (i : ℕ)) * (2 ^ (p * (a - i)) - 1) := fun i => by
    have hi : (i : ℕ) ≤ a := i.2.le
    have e1 : (2 ^ p) ^ a = 2 ^ (p * (i : ℕ)) * 2 ^ (p * (a - i)) := by
      rw [← pow_add, ← mul_add, Nat.add_sub_cancel' hi, pow_mul]
    rw [e1, Nat.mul_sub_one, pow_mul]
  have hne1 : ∀ i : Fin a, 2 ^ (p * (a - i)) - 1 ≠ 0 := fun i => by
    have hi : 1 ≤ a - (i : ℕ) := by have := i.2; omega
    have := two_le_two_pow_mul hp1 hi
    omega
  simp only [hfac]
  rw [padicValNat_three_prod _ _
    (fun i _ => mul_ne_zero (pow_ne_zero _ two_ne_zero) (hne1 i))]
  have hterm : ∀ i : Fin a, padicValNat 3 (2 ^ (p * (i : ℕ)) * (2 ^ (p * (a - i)) - 1)) =
      (a - (i : ℕ) + 1) % 2 := fun i => by
    have hi1 : 1 ≤ a - (i : ℕ) := by have := i.2; omega
    have hi5 : a - (i : ℕ) ≤ 5 := by omega
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) (hne1 i),
      padicValNat.eq_zero_of_not_dvd (not_three_dvd_two_pow _), zero_add,
      padicValNat_three_two_pow_mul_sub_one hp hi1 hi5]
  simp only [hterm]
  interval_cases a <;> simp [Fin.sum_univ_succ]

end OLThreeAdic

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

module
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.Permutation.SylowTwoNormalizer.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.Gross82.FieldOrder

open CFSG.ComponentClassification.CatLeaf Finset

private theorem cube_mod_three (x : ℕ) : x ^ 3 % 3 = x % 3 := by
  have h : x % 3 < 3 := Nat.mod_lt x (by decide)
  interval_cases hx : x % 3 <;> simp [Nat.pow_mod, hx]

private theorem pow_mod_three_one {x : ℕ} (hx : x % 3 = 1) (i : ℕ) :
    x ^ i % 3 = 1 := by
  simp [Nat.pow_mod, hx]

private theorem even_pow_mod_three_two {x i : ℕ} (hx : x % 3 = 2) (hi : Even i) :
    x ^ i % 3 = 1 := by
  obtain ⟨j, hj⟩ := hi
  have hij : i = 2 * j := by omega
  rw [hij, pow_mul, Nat.pow_mod]
  have hx2 : x ^ 2 % 3 = 1 := by simp [Nat.pow_mod, hx]
  rw [hx2]
  simp

private theorem odd_pow_mod_three_two {x i : ℕ} (hx : x % 3 = 2) (hi : Odd i) :
    x ^ i % 3 = 2 := by
  obtain ⟨j, hj⟩ := hi
  have hij : i = 2 * j + 1 := by omega
  rw [hij, pow_succ, Nat.mul_mod]
  rw [pow_mul, Nat.pow_mod]
  have hx2 : x ^ 2 % 3 = 1 := by simp [Nat.pow_mod, hx]
  rw [hx2, hx]
  simp

private theorem cube_sub_one_val {x : ℕ} (hx : 2 ≤ x) :
    padicValNat 3 (x ^ 3 - 1) =
      padicValNat 3 (x - 1) + if 3 ∣ x - 1 then 1 else 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hdiv : 3 ∣ x - 1
  · rw [if_pos hdiv]
    have hnx : ¬ 3 ∣ x := by omega
    have h := padicValNat.pow_sub_pow (p := 3) (by decide) (x := x) (y := 1)
      (by omega) hdiv hnx (n := 3) (by decide)
    simpa [padicValNat_self] using h
  · have hpow : 2 ≤ x ^ 3 := by
      have := Nat.one_lt_pow (by decide : 3 ≠ 0) (by omega : 1 < x)
      omega
    have hm := cube_mod_three x
    have hdiv' : ¬ 3 ∣ x ^ 3 - 1 := by omega
    rw [if_neg hdiv, padicValNat.eq_zero_of_not_dvd hdiv,
      padicValNat.eq_zero_of_not_dvd hdiv']

private theorem cube_add_one_val (x : ℕ) :
    padicValNat 3 (x ^ 3 + 1) =
      padicValNat 3 (x + 1) + if 3 ∣ x + 1 then 1 else 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hdiv : 3 ∣ x + 1
  · rw [if_pos hdiv]
    have hnx : ¬ 3 ∣ x := by omega
    have h := padicValNat.pow_add_pow (p := 3) (by decide) (x := x) (y := 1)
      hdiv hnx (n := 3) (by decide)
    simpa [padicValNat_self] using h
  · have hm := cube_mod_three x
    have hdiv' : ¬ 3 ∣ x ^ 3 + 1 := by omega
    rw [if_neg hdiv, padicValNat.eq_zero_of_not_dvd hdiv,
      padicValNat.eq_zero_of_not_dvd hdiv']

private theorem minus_factor_cube {s i : ℕ} (hs : 2 ≤ s) (hi : 0 < i) :
    padicValNat 3 ((s ^ 3) ^ i - 1) =
      padicValNat 3 (s ^ i - 1) + if 3 ∣ s ^ i - 1 then 1 else 0 := by
  have hp : (s ^ 3) ^ i = (s ^ i) ^ 3 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 i]
  rw [hp]
  exact cube_sub_one_val (by have := Nat.one_lt_pow hi.ne' (by omega : 1 < s); omega)

private theorem plus_factor_cube (s i : ℕ) :
    padicValNat 3 ((s ^ 3) ^ i + 1) =
      padicValNat 3 (s ^ i + 1) + if 3 ∣ s ^ i + 1 then 1 else 0 := by
  have hp : (s ^ 3) ^ i = (s ^ i) ^ 3 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 i]
  rw [hp]
  exact cube_add_one_val _

private theorem numerator_psl_val {s n : ℕ} (hs : 2 ≤ s) :
    padicValNat 3 (lieOrderNumerator .PSL n s) =
      (n * (n - 1) / 2) * padicValNat 3 s +
        ∑ i ∈ Icc 2 n, padicValNat 3 (s ^ i - 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ∀ i ∈ Icc 2 n, s ^ i - 1 ≠ 0 := by
    intro i hi
    have h := (mem_Icc.mp hi).1
    exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) (by omega))
  rw [lieOrderNumerator, padicValNat.mul (pow_ne_zero _ (by omega))
    (prod_ne_zero_iff.mpr hne), padicValNat.pow,
    CFSG.Permutation.SylowTwoNormalizer.padicValNat_prod _ hne]

private theorem numerator_psu_val {s n : ℕ} (hs : 2 ≤ s) :
    padicValNat 3 (lieOrderNumerator .PSU n s) =
      (n * (n - 1) / 2) * padicValNat 3 s +
        ∑ i ∈ Icc 2 n, padicValNat 3 (if Even i then s ^ i - 1 else s ^ i + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ∀ i ∈ Icc 2 n, (if Even i then s ^ i - 1 else s ^ i + 1) ≠ 0 := by
    intro i hi
    split_ifs
    · have h := (mem_Icc.mp hi).1
      exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) (by omega))
    · omega
  rw [lieOrderNumerator, padicValNat.mul (pow_ne_zero _ (by omega))
    (prod_ne_zero_iff.mpr hne), padicValNat.pow,
    CFSG.Permutation.SylowTwoNormalizer.padicValNat_prod _ hne]

private theorem degree_divisor_val_le {n x : ℕ} (hn : 2 ≤ n) :
    padicValNat 3 (Nat.gcd n x) ≤ padicValNat 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (padicValNat_dvd_iff_le (by omega : n ≠ 0)).mp
    (pow_padicValNat_dvd.trans (Nat.gcd_dvd_left n x))

private theorem degree_divisor_val_lt {n x : ℕ} (hn : 2 ≤ n) :
    padicValNat 3 (Nat.gcd n x) < n - 1 := by
  have h := degree_divisor_val_le (x := x) hn
  have hval := mul_padicValNat_le (p := 3) (n := n)
  omega

private theorem numerator_psl_cube {s n : ℕ} (hs : 2 ≤ s) :
    padicValNat 3 (lieOrderNumerator .PSL n (s ^ 3)) =
      padicValNat 3 (lieOrderNumerator .PSL n s) +
        2 * (n * (n - 1) / 2) * padicValNat 3 s +
          ∑ i ∈ Icc 2 n, (if 3 ∣ s ^ i - 1 then 1 else 0) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : 2 ≤ s ^ 3 := by
    have := Nat.one_lt_pow (by decide : 3 ≠ 0) (by omega : 1 < s)
    omega
  rw [numerator_psl_val hs3, numerator_psl_val hs, padicValNat.pow]
  have hsum : (∑ i ∈ Icc 2 n, padicValNat 3 ((s ^ 3) ^ i - 1)) =
      (∑ i ∈ Icc 2 n, padicValNat 3 (s ^ i - 1)) +
        ∑ i ∈ Icc 2 n, (if 3 ∣ s ^ i - 1 then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => minus_factor_cube hs
      (by have := (mem_Icc.mp hi).1; omega)
  rw [hsum]
  ring

private theorem numerator_psu_cube {s n : ℕ} (hs : 2 ≤ s) :
    padicValNat 3 (lieOrderNumerator .PSU n (s ^ 3)) =
      padicValNat 3 (lieOrderNumerator .PSU n s) +
        2 * (n * (n - 1) / 2) * padicValNat 3 s +
          ∑ i ∈ Icc 2 n,
            (if 3 ∣ (if Even i then s ^ i - 1 else s ^ i + 1) then 1 else 0) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : 2 ≤ s ^ 3 := by
    have := Nat.one_lt_pow (by decide : 3 ≠ 0) (by omega : 1 < s)
    omega
  rw [numerator_psu_val hs3, numerator_psu_val hs, padicValNat.pow]
  have hsum : (∑ i ∈ Icc 2 n,
      padicValNat 3 (if Even i then (s ^ 3) ^ i - 1 else (s ^ 3) ^ i + 1)) =
      (∑ i ∈ Icc 2 n, padicValNat 3 (if Even i then s ^ i - 1 else s ^ i + 1)) +
        ∑ i ∈ Icc 2 n,
          (if 3 ∣ (if Even i then s ^ i - 1 else s ^ i + 1) then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases he : Even i
    · simp only [if_pos he]
      exact minus_factor_cube hs (by have := (mem_Icc.mp hi).1; omega)
    · simp only [if_neg he]
      exact plus_factor_cube _ _
  rw [hsum]
  ring

private theorem sum_psl_mod_one {s n : ℕ} (hs : 2 ≤ s) (hm : s % 3 = 1) :
    (∑ i ∈ Icc 2 n, (if 3 ∣ s ^ i - 1 then 1 else 0)) = n - 1 := by
  have hsum : (∑ i ∈ Icc 2 n, (if 3 ∣ s ^ i - 1 then 1 else 0)) =
      ∑ i ∈ Icc 2 n, (1 : ℕ) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hp := pow_mod_three_one hm i
    have hpos : 1 ≤ s ^ i := Nat.one_le_pow _ _ (by omega)
    rw [if_pos (by omega : 3 ∣ s ^ i - 1)]
  rw [hsum, Finset.sum_const, Nat.card_Icc]
  simp only [smul_eq_mul, mul_one]
  omega

private theorem sum_psu_mod_two {s n : ℕ} (hs : 2 ≤ s) (hm : s % 3 = 2) :
    (∑ i ∈ Icc 2 n,
      (if 3 ∣ (if Even i then s ^ i - 1 else s ^ i + 1) then 1 else 0)) = n - 1 := by
  have hsum : (∑ i ∈ Icc 2 n,
      (if 3 ∣ (if Even i then s ^ i - 1 else s ^ i + 1) then 1 else 0)) =
      ∑ i ∈ Icc 2 n, (1 : ℕ) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases he : Even i
    · simp only [if_pos he]
      have hp := even_pow_mod_three_two hm he
      have hpos : 1 ≤ s ^ i := Nat.one_le_pow _ _ (by omega)
      rw [if_pos (by omega : 3 ∣ s ^ i - 1)]
    · simp only [if_neg he]
      have hp := odd_pow_mod_three_two hm (Nat.not_even_iff_odd.mp he)
      rw [if_pos (by omega : 3 ∣ s ^ i + 1)]
  rw [hsum, Finset.sum_const, Nat.card_Icc]
  simp only [smul_eq_mul, mul_one]
  omega

private theorem degree_exponent_pos {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ n * (n - 1) / 2 := by
  have h : 2 ≤ n * (n - 1) :=
    (show 2 * 1 ≤ n * (n - 1) from Nat.mul_le_mul hn (by omega))
  omega

private theorem sum_psl_pos {s n : ℕ} (hs : 2 ≤ s) (hn : 2 ≤ n) (h3 : ¬ 3 ∣ s) :
    1 ≤ ∑ i ∈ Icc 2 n, (if 3 ∣ s ^ i - 1 then 1 else 0) := by
  have hm : s % 3 = 1 ∨ s % 3 = 2 := by omega
  have hs2 : s ^ 2 % 3 = 1 := by
    rcases hm with h | h <;> simp [Nat.pow_mod, h]
  have hpos : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hdiv : 3 ∣ s ^ 2 - 1 := by omega
  have h := Finset.single_le_sum (f := fun i => if 3 ∣ s ^ i - 1 then 1 else 0)
    (fun i _ => Nat.zero_le _) (show 2 ∈ Icc 2 n by simp [hn])
  simpa only [if_pos hdiv] using h

private theorem sum_psu_pos {s n : ℕ} (hs : 2 ≤ s) (hn : 2 ≤ n) (h3 : ¬ 3 ∣ s) :
    1 ≤ ∑ i ∈ Icc 2 n,
      (if 3 ∣ (if Even i then s ^ i - 1 else s ^ i + 1) then 1 else 0) := by
  have hm : s % 3 = 1 ∨ s % 3 = 2 := by omega
  have hs2 : s ^ 2 % 3 = 1 := by
    rcases hm with h | h <;> simp [Nat.pow_mod, h]
  have hpos : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hdiv : 3 ∣ s ^ 2 - 1 := by omega
  have h := Finset.single_le_sum
    (f := fun i => if 3 ∣ (if Even i then s ^ i - 1 else s ^ i + 1) then 1 else 0)
    (fun i _ => Nat.zero_le _) (show 2 ∈ Icc 2 n by simp [hn])
  simpa only [show Even 2 from by decide, if_pos, if_pos hdiv] using h

theorem padicValNat_three_lieOrder_psl_cube_lt {s n : ℕ} (hs : 2 ≤ s) (hn : 2 ≤ n) :
    padicValNat 3 (lieOrderNumerator .PSL n s) +
      padicValNat 3 (lieOrderDivisor .PSL n (s ^ 3)) <
    padicValNat 3 (lieOrderNumerator .PSL n (s ^ 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [numerator_psl_cube hs]
  by_cases hdiv : 3 ∣ s
  · have hpow : 3 ∣ s ^ 3 := hdiv.trans (dvd_pow_self s (by decide : 3 ≠ 0))
    have hg : ¬ 3 ∣ Nat.gcd n (s ^ 3 - 1) := by
      intro hg
      have := hg.trans (Nat.gcd_dvd_right n (s ^ 3 - 1))
      have hp : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    rw [lieOrderDivisor, padicValNat.eq_zero_of_not_dvd hg]
    have hexp := degree_exponent_pos hn
    have hv : 1 ≤ padicValNat 3 s := one_le_padicValNat_of_dvd (by omega) hdiv
    have hprod : 1 ≤ 2 * (n * (n - 1) / 2) * padicValNat 3 s := by nlinarith
    omega
  · have hm : s % 3 = 1 ∨ s % 3 = 2 := by omega
    rcases hm with hm | hm
    · have hd := degree_divisor_val_lt (x := s ^ 3 - 1) hn
      rw [sum_psl_mod_one hs hm, lieOrderDivisor]
      omega
    · have hm3 := cube_mod_three s
      have hg : ¬ 3 ∣ Nat.gcd n (s ^ 3 - 1) := by
        intro h
        have := h.trans (Nat.gcd_dvd_right n (s ^ 3 - 1))
        have hp : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ (by omega)
        omega
      rw [lieOrderDivisor, padicValNat.eq_zero_of_not_dvd hg]
      have hsum := sum_psl_pos hs hn hdiv
      omega

theorem padicValNat_three_lieOrder_psu_cube_lt {s n : ℕ} (hs : 2 ≤ s) (hn : 2 ≤ n) :
    padicValNat 3 (lieOrderNumerator .PSU n s) +
      padicValNat 3 (lieOrderDivisor .PSU n (s ^ 3)) <
    padicValNat 3 (lieOrderNumerator .PSU n (s ^ 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [numerator_psu_cube hs]
  by_cases hdiv : 3 ∣ s
  · have hpow : 3 ∣ s ^ 3 := hdiv.trans (dvd_pow_self s (by decide : 3 ≠ 0))
    have hg : ¬ 3 ∣ Nat.gcd n (s ^ 3 + 1) := by
      intro hg
      have := hg.trans (Nat.gcd_dvd_right n (s ^ 3 + 1))
      omega
    rw [lieOrderDivisor, padicValNat.eq_zero_of_not_dvd hg]
    have hexp := degree_exponent_pos hn
    have hv : 1 ≤ padicValNat 3 s := one_le_padicValNat_of_dvd (by omega) hdiv
    have hprod : 1 ≤ 2 * (n * (n - 1) / 2) * padicValNat 3 s := by nlinarith
    omega
  · have hm : s % 3 = 1 ∨ s % 3 = 2 := by omega
    rcases hm with hm | hm
    · have hm3 := cube_mod_three s
      have hg : ¬ 3 ∣ Nat.gcd n (s ^ 3 + 1) := by
        intro h
        have := h.trans (Nat.gcd_dvd_right n (s ^ 3 + 1))
        omega
      rw [lieOrderDivisor, padicValNat.eq_zero_of_not_dvd hg]
      have hsum := sum_psu_pos hs hn hdiv
      omega
    · have hd := degree_divisor_val_lt (x := s ^ 3 + 1) hn
      rw [sum_psu_mod_two hs hm, lieOrderDivisor]
      omega

end CFSG.LocalAnalysis.Gross82.FieldOrder

module

public import CFSG.Open.Defs

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open CFSG.Open

theorem arith_three_pow_five_dvd_even_factors {q : ℕ} (hq3 : ¬ 3 ∣ q) :
    3 ^ 5 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) := by
  have hr : q % 3 = 1 ∨ q % 3 = 2 := by omega
  have hr9 : q % 9 = 1 ∨ q % 9 = 2 ∨ q % 9 = 4 ∨ q % 9 = 5 ∨ q % 9 = 7 ∨ q % 9 = 8 := by
    omega
  have h2 : q ^ 2 % 3 = 1 := by
    rcases hr with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have h4 : q ^ 4 % 3 = 1 := by
    rcases hr with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have h8 : q ^ 8 % 3 = 1 := by
    rcases hr with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have h6 : q ^ 6 % 9 = 1 := by
    rcases hr9 with h | h | h | h | h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have d2 : 3 ∣ q ^ 2 - 1 := by omega
  have d4 : 3 ∣ q ^ 4 - 1 := by omega
  have d6 : 9 ∣ q ^ 6 - 1 := by omega
  have d8 : 3 ∣ q ^ 8 - 1 := by omega
  have key := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul d2 d4) d6) d8
  rw [show (3 : ℕ) ^ 5 = 3 * 3 * 9 * 3 by norm_num]
  exact key

theorem arith_three_pow_five_dvd_prod_even {n q : ℕ} (f : ℕ → ℕ) (hn : 8 ≤ n) (hq3 : ¬ 3 ∣ q)
    (hf : ∀ i, Even i → f i = q ^ i - 1) :
    3 ^ 5 ∣ ∏ i ∈ Finset.Icc 2 n, f i := by
  have hsub : ({2, 4, 6, 8} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  have h2 : (2 : ℕ) ∉ ({4, 6, 8} : Finset ℕ) := by decide
  have h4 : (4 : ℕ) ∉ ({6, 8} : Finset ℕ) := by decide
  have h6 : (6 : ℕ) ∉ ({8} : Finset ℕ) := by decide
  calc 3 ^ 5 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) :=
        arith_three_pow_five_dvd_even_factors hq3
    _ = f 2 * (f 4 * (f 6 * f 8)) := by
        rw [hf 2 even_two, hf 4 ⟨2, rfl⟩, hf 6 ⟨3, rfl⟩, hf 8 ⟨4, rfl⟩]
        ring
    _ = ∏ i ∈ ({2, 4, 6, 8} : Finset ℕ), f i := by
        rw [Finset.prod_insert h2, Finset.prod_insert h4, Finset.prod_insert h6,
          Finset.prod_singleton]
    _ ∣ ∏ i ∈ Finset.Icc 2 n, f i := Finset.prod_dvd_prod_of_subset _ _ _ hsub

theorem arith_dvd_div_mul {a g M : ℕ} (hg : 0 < g) (h : a * g ∣ M) (k : ℕ) :
    a ∣ k * M / g := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨k * c, ?_⟩
  rw [show k * (a * g * c) = g * (a * (k * c)) by ring, Nat.mul_div_cancel_left _ hg]

theorem arith_three_pow_five_mul_gcd_dvd {n d : ℕ} (f : ℕ → ℕ) (hn : 8 ≤ n)
    (hd : ∀ i ∈ Finset.Icc 2 n, d ∣ f i) (h3 : 3 ^ 5 ∣ ∏ i ∈ Finset.Icc 2 n, f i) :
    3 ^ 5 * Nat.gcd n d ∣ ∏ i ∈ Finset.Icc 2 n, f i := by
  have h2 : 2 ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr ⟨le_refl 2, by omega⟩
  have hgd : Nat.gcd n d ∣ ∏ i ∈ Finset.Icc 2 n, f i :=
    (Nat.gcd_dvd_right n d).trans ((hd 2 h2).trans (Finset.dvd_prod_of_mem f h2))
  by_cases h3d : 3 ∣ d
  · have hcard : (Finset.Icc 2 n).card = n - 1 := by
      rw [Nat.card_Icc]
      omega
    have hpow : d ^ (n - 1) ∣ ∏ i ∈ Finset.Icc 2 n, f i := by
      rw [← hcard, ← Finset.prod_const]
      exact Finset.prod_dvd_prod_of_dvd _ _ hd
    have h35 : 3 ^ 5 * d ∣ d ^ (n - 1) := by
      have e : d ^ (n - 1) = d ^ (n - 2) * d := by
        rw [← pow_succ, show n - 2 + 1 = n - 1 by omega]
      rw [e]
      exact mul_dvd_mul_right
        ((pow_dvd_pow 3 (by omega : 5 ≤ n - 2)).trans (pow_dvd_pow_of_dvd h3d (n - 2))) d
    exact (mul_dvd_mul_left (3 ^ 5) (Nat.gcd_dvd_right n d)).trans (h35.trans hpow)
  · have hcop : Nat.Coprime (3 ^ 5) (Nat.gcd n d) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      exact fun h => h3d (h.trans (Nat.gcd_dvd_right n d))
    exact hcop.mul_dvd_of_dvd_of_dvd h3 hgd

theorem arith_twisted_nonneg {q : ℕ} (hq1 : 1 ≤ q) (i : ℕ) :
    0 ≤ (q : ℤ) ^ i - (-1 : ℤ) ^ i := by
  have h1 : (1 : ℤ) ≤ (q : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast hq1)
  rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> linarith

theorem arith_twisted_dvd {q : ℕ} (hq1 : 1 ≤ q) (i : ℕ) :
    q + 1 ∣ ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
  rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg (arith_twisted_nonneg hq1 i)]
  have h := sub_dvd_pow_sub_pow (q : ℤ) (-1) i
  rw [sub_neg_eq_add] at h
  push_cast
  exact h

theorem arith_toNat_even {q : ℕ} (hq1 : 1 ≤ q) {i : ℕ} (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq1
  have e : (q : ℤ) ^ i - 1 = ((q ^ i - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  rw [hi.neg_one_pow, e, Int.toNat_natCast]

theorem three_pow_five_dvd_ordA {n q : ℕ} (hn : 8 ≤ n) (hq3 : ¬ 3 ∣ q) :
    3 ^ 5 ∣ ordA (n - 1) q := by
  have hn1 : n - 1 + 1 = n := by omega
  have hg : 0 < Nat.gcd n (q - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  unfold ordA
  rw [hn1]
  refine arith_dvd_div_mul hg ?_ _
  refine arith_three_pow_five_mul_gcd_dvd (fun i => q ^ i - 1) hn ?_
    (arith_three_pow_five_dvd_prod_even (fun i => q ^ i - 1) hn hq3 (fun i _ => rfl))
  intro i _
  have h := Nat.sub_dvd_pow_sub_pow q 1 i
  rw [one_pow] at h
  exact h

theorem three_pow_five_dvd_ordTwistedA {n q : ℕ} (hn : 8 ≤ n) (hq3 : ¬ 3 ∣ q) :
    3 ^ 5 ∣ ordTwistedA (n - 1) q := by
  have hn1 : n - 1 + 1 = n := by omega
  have hg : 0 < Nat.gcd n (q + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hq1 : 1 ≤ q := by omega
  unfold ordTwistedA
  rw [hn1]
  refine arith_dvd_div_mul hg ?_ _
  refine arith_three_pow_five_mul_gcd_dvd (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) hn
    (fun i _ => arith_twisted_dvd hq1 i) ?_
  exact arith_three_pow_five_dvd_prod_even (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) hn hq3
    (fun i hi => arith_toNat_even hq1 hi)

end CFSG.ComponentClassification.CatFC.KGHS3

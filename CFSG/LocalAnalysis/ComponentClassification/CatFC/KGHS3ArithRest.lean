module

public import CFSG.Open.Defs

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open CFSG.Open

theorem rest_three_dvd_sq_sub_one {q : ℕ} (hq3 : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have hr : q % 3 = 1 ∨ q % 3 = 2 := by omega
  have h2 : q ^ 2 % 3 = 1 := by
    rcases hr with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  omega

theorem rest_sub_one_dvd_pow (q i : ℕ) : q - 1 ∣ q ^ i - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow q 1 i
  rwa [one_pow] at h

theorem rest_sq_sub_one_dvd (q j : ℕ) : q ^ 2 - 1 ∣ q ^ (2 * j) - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 j
  rwa [one_pow, ← pow_mul] at h

theorem rest_three_dvd_sq {q : ℕ} (hq3 : ¬ 3 ∣ q) (j : ℕ) : 3 ∣ q ^ (2 * j) - 1 :=
  (rest_three_dvd_sq_sub_one hq3).trans (rest_sq_sub_one_dvd q j)

theorem rest_nine_dvd_six {q : ℕ} (hq3 : ¬ 3 ∣ q) : 9 ∣ q ^ 6 - 1 := by
  have hr : q % 9 = 1 ∨ q % 9 = 2 ∨ q % 9 = 4 ∨ q % 9 = 5 ∨ q % 9 = 7 ∨ q % 9 = 8 := by
    omega
  have h6 : q ^ 6 % 9 = 1 := by
    rcases hr with h | h | h | h | h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  omega

theorem rest_three_pow_five_dvd_four {a b c d : ℕ} (ha : 3 ∣ a) (hb : 3 ∣ b) (hc : 9 ∣ c)
    (hd : 3 ∣ d) : 3 ^ 5 ∣ a * b * c * d := by
  have h := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha hb) hc) hd
  exact (by norm_num : (3 : ℕ) ^ 5 ∣ 3 * 3 * 9 * 3).trans h

theorem rest_four_factors_dvd (f : ℕ → ℕ) {m : ℕ} (hm : 4 ≤ m) :
    f 1 * f 2 * f 3 * f 4 ∣ ∏ i ∈ Finset.Icc 1 m, f i := by
  have hsub : ({1, 2, 3, 4} : Finset ℕ) ⊆ Finset.Icc 1 m := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  have e : ∏ i ∈ ({1, 2, 3, 4} : Finset ℕ), f i = f 1 * f 2 * f 3 * f 4 := by
    rw [Finset.prod_insert (show (1 : ℕ) ∉ ({2, 3, 4} : Finset ℕ) by decide),
      Finset.prod_insert (show (2 : ℕ) ∉ ({3, 4} : Finset ℕ) by decide),
      Finset.prod_insert (show (3 : ℕ) ∉ ({4} : Finset ℕ) by decide), Finset.prod_singleton]
    simp only [mul_assoc]
  rw [← e]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

theorem rest_three_factors_dvd (f : ℕ → ℕ) {m : ℕ} (hm : 3 ≤ m) :
    f 1 * f 2 * f 3 ∣ ∏ i ∈ Finset.Icc 1 m, f i := by
  have hsub : ({1, 2, 3} : Finset ℕ) ⊆ Finset.Icc 1 m := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  have e : ∏ i ∈ ({1, 2, 3} : Finset ℕ), f i = f 1 * f 2 * f 3 := by
    rw [Finset.prod_insert (show (1 : ℕ) ∉ ({2, 3} : Finset ℕ) by decide),
      Finset.prod_insert (show (2 : ℕ) ∉ ({3} : Finset ℕ) by decide), Finset.prod_singleton]
    simp only [mul_assoc]
  rw [← e]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

theorem rest_pow_five_dvd_prod {q m : ℕ} (hm : 4 ≤ m) (hq3 : ¬ 3 ∣ q) :
    3 ^ 5 ∣ ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) :=
  (rest_three_pow_five_dvd_four (rest_three_dvd_sq hq3 1) (rest_three_dvd_sq hq3 2)
    (rest_nine_dvd_six hq3) (rest_three_dvd_sq hq3 4)).trans
    (rest_four_factors_dvd (fun i => q ^ (2 * i) - 1) hm)

theorem rest_pow_four_dvd_prod {q m : ℕ} (hm : 3 ≤ m) (hq3 : ¬ 3 ∣ q) :
    3 ^ 4 ∣ ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) := by
  have h : (3 * 3 * 9 : ℕ) ∣ (q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1) * (q ^ (2 * 3) - 1) :=
    mul_dvd_mul (mul_dvd_mul (rest_three_dvd_sq hq3 1) (rest_three_dvd_sq hq3 2))
      (rest_nine_dvd_six hq3)
  exact (by norm_num : (3 : ℕ) ^ 4 ∣ 3 * 3 * 9).trans
    (h.trans (rest_three_factors_dvd (fun i => q ^ (2 * i) - 1) hm))

theorem rest_dvd_div_of_coprime {k g X : ℕ} (hgX : g ∣ X) (hcop : Nat.Coprime k g)
    (hk : k ∣ X) : k ∣ X / g := by
  apply Nat.Coprime.dvd_of_dvd_mul_right hcop
  rw [Nat.div_mul_cancel hgX]
  exact hk

theorem rest_three_pow_five_dvd_ordD_core {n q : ℕ} (hn : 4 ≤ n) (hq3 : ¬ 3 ∣ q) :
    3 ^ 5 ∣ (q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · have h3n : 3 ∣ q ^ n - 1 := by
      have h := rest_three_dvd_sq hq3 (n / 2)
      rwa [show 2 * (n / 2) = n by omega] at h
    exact (show (3 : ℕ) ^ 5 ∣ 3 * 3 ^ 4 by norm_num).trans
      (mul_dvd_mul h3n (rest_pow_four_dvd_prod (m := n - 1) (by omega) hq3))
  · exact Dvd.dvd.mul_left (rest_pow_five_dvd_prod (m := n - 1) (by omega) hq3) _

theorem three_pow_five_dvd_ordBC {n q : ℕ} (hn : 4 ≤ n) (hq3 : ¬ 3 ∣ q) :
    3 ^ 5 ∣ ordBC n q := by
  unfold ordBC
  have hR : 3 ^ 5 ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := rest_pow_five_dvd_prod hn hq3
  have hg : Nat.gcd 2 (q - 1) ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩
    exact (Nat.gcd_dvd_right _ _).trans
      ((rest_sub_one_dvd_pow q (2 * 1)).trans
        (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1))
  apply rest_dvd_div_of_coprime
  · exact Dvd.dvd.mul_left hg _
  · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
  · exact Dvd.dvd.mul_left hR _

theorem three_pow_five_dvd_ordD {n q : ℕ} (hn : 4 ≤ n) (hq3 : ¬ 3 ∣ q) :
    3 ^ 5 ∣ ordD n q := by
  unfold ordD
  apply rest_dvd_div_of_coprime
  · exact (Nat.gcd_dvd_right _ _).trans
      (dvd_mul_of_dvd_left (dvd_mul_left (q ^ n - 1) (q ^ (n * (n - 1)))) _)
  · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
  · rw [mul_assoc]
    exact dvd_mul_of_dvd_right (rest_three_pow_five_dvd_ordD_core hn hq3) _

theorem three_pow_five_dvd_ordTwistedD {n q : ℕ} (hn : 5 ≤ n) (hq3 : ¬ 3 ∣ q) :
    3 ^ 5 ∣ ordTwistedD n q := by
  unfold ordTwistedD
  apply rest_dvd_div_of_coprime
  · exact (Nat.gcd_dvd_right _ _).trans
      (dvd_mul_of_dvd_left (dvd_mul_left (q ^ n + 1) (q ^ (n * (n - 1)))) _)
  · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
  · exact dvd_mul_of_dvd_right (rest_pow_five_dvd_prod (m := n - 1) (by omega) hq3) _

theorem three_pow_five_dvd_ordF4 {q : ℕ} (hq3 : ¬ 3 ∣ q) : 3 ^ 5 ∣ ordF4 q := by
  unfold ordF4
  have h12 : 3 ∣ q ^ 12 - 1 := rest_three_dvd_sq hq3 6
  have h8 : 3 ∣ q ^ 8 - 1 := rest_three_dvd_sq hq3 4
  have h6 : 9 ∣ q ^ 6 - 1 := rest_nine_dvd_six hq3
  have h2 : 3 ∣ q ^ 2 - 1 := rest_three_dvd_sq_sub_one hq3
  have k1 := mul_dvd_mul (one_dvd (q ^ 24)) h12
  have k2 := mul_dvd_mul k1 h8
  have k3 := mul_dvd_mul k2 h6
  have k4 := mul_dvd_mul k3 h2
  exact (by norm_num : (3 : ℕ) ^ 5 ∣ 1 * 3 * 3 * 9 * 3).trans k4

theorem three_pow_five_dvd_ordE6 {q : ℕ} (hq3 : ¬ 3 ∣ q) : 3 ^ 5 ∣ ordE6 q := by
  unfold ordE6
  have h12 : 3 ∣ q ^ 12 - 1 := rest_three_dvd_sq hq3 6
  have h8 : 3 ∣ q ^ 8 - 1 := rest_three_dvd_sq hq3 4
  have h6 : 9 ∣ q ^ 6 - 1 := rest_nine_dvd_six hq3
  have h2 : 3 ∣ q ^ 2 - 1 := rest_three_dvd_sq_sub_one hq3
  by_cases h : 3 ∣ q - 1
  · rw [Nat.gcd_eq_left h]
    apply Nat.dvd_div_of_mul_dvd
    have h9 : 3 ∣ q ^ 9 - 1 := h.trans (rest_sub_one_dvd_pow q 9)
    have h5 : 3 ∣ q ^ 5 - 1 := h.trans (rest_sub_one_dvd_pow q 5)
    have k1 := mul_dvd_mul (one_dvd (q ^ 36)) h12
    have k2 := mul_dvd_mul k1 h9
    have k3 := mul_dvd_mul k2 h8
    have k4 := mul_dvd_mul k3 h6
    have k5 := mul_dvd_mul k4 h5
    have k6 := mul_dvd_mul k5 h2
    exact (by norm_num : (3 : ℕ) * 3 ^ 5 ∣ 1 * 3 * 3 * 3 * 9 * 3 * 3).trans k6
  · have hc : Nat.gcd 3 (q - 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h
    rw [hc, Nat.div_one]
    have k1 := mul_dvd_mul (one_dvd (q ^ 36)) h12
    have k2 := mul_dvd_mul k1 (one_dvd (q ^ 9 - 1))
    have k3 := mul_dvd_mul k2 h8
    have k4 := mul_dvd_mul k3 h6
    have k5 := mul_dvd_mul k4 (one_dvd (q ^ 5 - 1))
    have k6 := mul_dvd_mul k5 h2
    exact (by norm_num : (3 : ℕ) ^ 5 ∣ 1 * 3 * 1 * 3 * 9 * 1 * 3).trans k6

theorem rest_add_one_dvd_odd_pow (q : ℕ) {k : ℕ} (hk : Odd k) : q + 1 ∣ q ^ k + 1 := by
  have h := Odd.nat_add_dvd_pow_add_pow q 1 hk
  rwa [one_pow] at h

theorem three_pow_five_dvd_ordTwistedE6 {q : ℕ} (hq3 : ¬ 3 ∣ q) : 3 ^ 5 ∣ ordTwistedE6 q := by
  unfold ordTwistedE6
  have h12 : 3 ∣ q ^ 12 - 1 := rest_three_dvd_sq hq3 6
  have h8 : 3 ∣ q ^ 8 - 1 := rest_three_dvd_sq hq3 4
  have h6 : 9 ∣ q ^ 6 - 1 := rest_nine_dvd_six hq3
  have h2 : 3 ∣ q ^ 2 - 1 := rest_three_dvd_sq_sub_one hq3
  by_cases h : 3 ∣ q + 1
  · rw [Nat.gcd_eq_left h]
    apply Nat.dvd_div_of_mul_dvd
    have h9 : 3 ∣ q ^ 9 + 1 := h.trans (rest_add_one_dvd_odd_pow q ⟨4, by norm_num⟩)
    have h5 : 3 ∣ q ^ 5 + 1 := h.trans (rest_add_one_dvd_odd_pow q ⟨2, by norm_num⟩)
    have k1 := mul_dvd_mul (one_dvd (q ^ 36)) h12
    have k2 := mul_dvd_mul k1 h9
    have k3 := mul_dvd_mul k2 h8
    have k4 := mul_dvd_mul k3 h6
    have k5 := mul_dvd_mul k4 h5
    have k6 := mul_dvd_mul k5 h2
    exact (by norm_num : (3 : ℕ) * 3 ^ 5 ∣ 1 * 3 * 3 * 3 * 9 * 3 * 3).trans k6
  · have hc : Nat.gcd 3 (q + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h
    rw [hc, Nat.div_one]
    have k1 := mul_dvd_mul (one_dvd (q ^ 36)) h12
    have k2 := mul_dvd_mul k1 (one_dvd (q ^ 9 + 1))
    have k3 := mul_dvd_mul k2 h8
    have k4 := mul_dvd_mul k3 h6
    have k5 := mul_dvd_mul k4 (one_dvd (q ^ 5 + 1))
    have k6 := mul_dvd_mul k5 h2
    exact (by norm_num : (3 : ℕ) ^ 5 ∣ 1 * 3 * 1 * 3 * 9 * 1 * 3).trans k6

theorem three_pow_five_dvd_ordE7 {q : ℕ} (hq3 : ¬ 3 ∣ q) : 3 ^ 5 ∣ ordE7 q := by
  unfold ordE7
  have h12 : 3 ∣ q ^ 12 - 1 := rest_three_dvd_sq hq3 6
  have h8 : 3 ∣ q ^ 8 - 1 := rest_three_dvd_sq hq3 4
  have h6 : 9 ∣ q ^ 6 - 1 := rest_nine_dvd_six hq3
  have h2 : 3 ∣ q ^ 2 - 1 := rest_three_dvd_sq_sub_one hq3
  apply rest_dvd_div_of_coprime
  · exact (Nat.gcd_dvd_right _ _).trans ((rest_sub_one_dvd_pow q 2).trans (dvd_mul_left _ _))
  · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
  · have k1 := mul_dvd_mul (one_dvd (q ^ 63)) (one_dvd (q ^ 18 - 1))
    have k2 := mul_dvd_mul k1 (one_dvd (q ^ 14 - 1))
    have k3 := mul_dvd_mul k2 h12
    have k4 := mul_dvd_mul k3 (one_dvd (q ^ 10 - 1))
    have k5 := mul_dvd_mul k4 h8
    have k6 := mul_dvd_mul k5 h6
    have k7 := mul_dvd_mul k6 h2
    exact (by norm_num : (3 : ℕ) ^ 5 ∣ 1 * 1 * 1 * 3 * 1 * 3 * 9 * 3).trans k7

theorem three_pow_five_dvd_ordE8 {q : ℕ} (hq3 : ¬ 3 ∣ q) : 3 ^ 5 ∣ ordE8 q := by
  unfold ordE8
  have h18 : 3 ∣ q ^ 18 - 1 := rest_three_dvd_sq hq3 9
  have h14 : 3 ∣ q ^ 14 - 1 := rest_three_dvd_sq hq3 7
  have h12 : 3 ∣ q ^ 12 - 1 := rest_three_dvd_sq hq3 6
  have h8 : 3 ∣ q ^ 8 - 1 := rest_three_dvd_sq hq3 4
  have h2 : 3 ∣ q ^ 2 - 1 := rest_three_dvd_sq_sub_one hq3
  have k1 := mul_dvd_mul (one_dvd (q ^ 120)) (one_dvd (q ^ 30 - 1))
  have k2 := mul_dvd_mul k1 (one_dvd (q ^ 24 - 1))
  have k3 := mul_dvd_mul k2 (one_dvd (q ^ 20 - 1))
  have k4 := mul_dvd_mul k3 h18
  have k5 := mul_dvd_mul k4 h14
  have k6 := mul_dvd_mul k5 h12
  have k7 := mul_dvd_mul k6 h8
  have k8 := mul_dvd_mul k7 h2
  exact (by norm_num : (3 : ℕ) ^ 5 ∣ 1 * 1 * 1 * 1 * 3 * 3 * 3 * 3 * 3).trans k8

theorem rest_ordTwistedF4_not_seven {q : ℕ} (hq : q % 7 = 2 ∨ q % 7 = 4) :
    ¬ 7 ∣ ordTwistedF4 q := by
  have h3 : q ^ 3 % 7 = 1 := by
    rcases hq with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have h6 : q ^ 6 % 7 = 1 := by
    rcases hq with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have h12 : q ^ 12 % 7 = 1 := by
    rcases hq with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have h4 : q ^ 4 % 7 = q % 7 := by
    rcases hq with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have hp : Nat.Prime 7 := by norm_num
  unfold ordTwistedF4
  intro h
  simp only [hp.dvd_mul] at h
  omega

theorem rest_two_pow_mod_seven {m : ℕ} (h3 : ¬ 3 ∣ m) : 2 ^ m % 7 = 2 ∨ 2 ^ m % 7 = 4 := by
  have hr : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have e : 2 ^ m = 8 ^ (m / 3) * 2 ^ (m % 3) := by
    conv_lhs => rw [← Nat.div_add_mod m 3]
    rw [pow_add, pow_mul]
    norm_num
  have h8 : 8 ^ (m / 3) % 7 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [e, Nat.mul_mod, h8, one_mul, Nat.mod_mod]
  rcases hr with h | h <;> rw [h] <;> norm_num

theorem rest_ordTwistedF4_three_pow_five {k : ℕ} (hk : Odd k) :
    3 ^ 5 ∣ ordTwistedF4 (2 ^ (3 * k)) := by
  have e4 : (2 ^ (3 * k)) ^ 4 = (2 ^ 6) ^ (2 * k) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have e3 : (2 ^ (3 * k)) ^ 3 = (2 ^ 9) ^ k := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have h9 : 9 ∣ (2 ^ (3 * k)) ^ 4 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ 6) 1 (2 * k)
    rw [one_pow] at h
    rw [e4]
    exact (by norm_num : (9 : ℕ) ∣ 2 ^ 6 - 1).trans h
  have h27 : 27 ∣ (2 ^ (3 * k)) ^ 3 + 1 := by
    rw [e3]
    have h := Odd.nat_add_dvd_pow_add_pow (2 ^ 9) 1 hk
    rw [one_pow] at h
    exact (by norm_num : (27 : ℕ) ∣ 2 ^ 9 + 1).trans h
  unfold ordTwistedF4
  have k1 := mul_dvd_mul (one_dvd ((2 ^ (3 * k)) ^ 12)) (one_dvd ((2 ^ (3 * k)) ^ 6 + 1))
  have k2 := mul_dvd_mul k1 h9
  have k3 := mul_dvd_mul k2 h27
  have k4 := mul_dvd_mul k3 (one_dvd (2 ^ (3 * k) - 1))
  exact (by norm_num : (3 : ℕ) ^ 5 ∣ 1 * 1 * 9 * 27 * 1).trans k4

theorem not_seven_dvd_or_three_pow_five_dvd_ordTwistedF4 {m : ℕ} (hm : Odd m) :
    ¬ 7 ∣ ordTwistedF4 (2 ^ m) ∨ 3 ^ 5 ∣ ordTwistedF4 (2 ^ m) := by
  by_cases h3 : 3 ∣ m
  · right
    obtain ⟨k, rfl⟩ := h3
    exact rest_ordTwistedF4_three_pow_five (Nat.odd_mul.mp hm).2
  · left
    exact rest_ordTwistedF4_not_seven (rest_two_pow_mod_seven h3)

end CFSG.ComponentClassification.CatFC.KGHS3

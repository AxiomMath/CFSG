module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.CrossArith

open CFSG.Open

section Basic

variable {q : ℕ}

theorem exists_sq_eq (hq : ¬ 3 ∣ q) : ∃ s, q ^ 2 = 3 * s + 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 1 ∨ q = 3 * k + 2 := ⟨q / 3, by omega⟩
  rcases hk with rfl | rfl
  · exact ⟨3 * k ^ 2 + 2 * k, by ring⟩
  · exact ⟨3 * k ^ 2 + 4 * k + 1, by ring⟩

theorem three_dvd_pow_two_mul_sub_one (hq : ¬ 3 ∣ q) (i : ℕ) : 3 ∣ q ^ (2 * i) - 1 := by
  obtain ⟨s, hs⟩ := exists_sq_eq hq
  have h2 : 3 ∣ q ^ 2 - 1 := ⟨s, by omega⟩
  exact h2.trans (Nat.pow_sub_one_dvd_pow_sub_one q (dvd_mul_right 2 i) :)

theorem three_dvd_sq_sub_one (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  simpa using three_dvd_pow_two_mul_sub_one hq 1

theorem nine_dvd_pow_six_sub_one (hq : ¬ 3 ∣ q) : 9 ∣ q ^ 6 - 1 := by
  obtain ⟨s, hs⟩ := exists_sq_eq hq
  have h6 : q ^ 6 = 9 * (3 * s ^ 3 + 3 * s ^ 2 + s) + 1 := by
    rw [show q ^ 6 = (q ^ 2) ^ 3 by ring, hs]; ring
  exact ⟨3 * s ^ 3 + 3 * s ^ 2 + s, by omega⟩

theorem not_three_dvd_sq_add_one (hq : ¬ 3 ∣ q) : ¬ 3 ∣ q ^ 2 + 1 := by
  obtain ⟨s, hs⟩ := exists_sq_eq hq
  omega

theorem nine_dvd_of_three_dvd_of_twentySeven_dvd_sq {t : ℕ} (h3 : 3 ∣ t) (h27 : 27 ∣ t ^ 2) :
    9 ∣ t := by
  obtain ⟨s, rfl⟩ := h3
  have : 3 ∣ s ^ 2 := by
    have h : 27 ∣ 9 * s ^ 2 := by simpa [mul_pow, mul_assoc] using h27
    omega
  have hs : 3 ∣ s := Nat.prime_three.dvd_of_dvd_pow this
  obtain ⟨u, rfl⟩ := hs
  exact ⟨u, by ring⟩

theorem eighty_one_dvd_of_twentySeven_dvd (hq : ¬ 3 ∣ q) {R : ℕ} (hR : ¬ 3 ∣ R)
    (h27 : 27 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) * R) : 81 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) * R := by
  obtain ⟨s, hs⟩ := exists_sq_eq hq
  have h4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    have := Nat.sq_sub_sq (q ^ 2) 1
    rw [one_pow, ← pow_mul] at this
    rw [show 2 * 2 = 4 from rfl] at this
    rw [this, mul_comm]
  have hcop : Nat.Coprime 27 ((q ^ 2 + 1) * R) := by
    refine Nat.Coprime.pow_left 3 (?_ : Nat.Coprime 3 _)
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact not_three_dvd_sq_add_one hq h
    · exact hR h
  have h27' : 27 ∣ (q ^ 2 - 1) ^ 2 * ((q ^ 2 + 1) * R) := by
    have : (q ^ 2 - 1) * (q ^ 4 - 1) * R = (q ^ 2 - 1) ^ 2 * ((q ^ 2 + 1) * R) := by
      rw [h4]; ring
    rwa [this] at h27
  have h27'' : 27 ∣ (q ^ 2 - 1) ^ 2 := hcop.dvd_of_dvd_mul_right h27'
  have h9 : 9 ∣ q ^ 2 - 1 :=
    nine_dvd_of_three_dvd_of_twentySeven_dvd_sq (three_dvd_sq_sub_one hq) h27''
  have h81 : 81 ∣ (q ^ 2 - 1) ^ 2 := by
    have := pow_dvd_pow_of_dvd h9 2
    simpa using this
  have : (q ^ 2 - 1) * (q ^ 4 - 1) * R = (q ^ 2 - 1) ^ 2 * ((q ^ 2 + 1) * R) := by
    rw [h4]; ring
  rw [this]
  exact Dvd.dvd.mul_right h81 _

end Basic

section Div

theorem dvd_div_iff_of_coprime {M g d : ℕ} (hg : g ∣ M) (hdg : Nat.Coprime d g) :
    d ∣ M / g ↔ d ∣ M := by
  constructor
  · intro h
    rw [← Nat.mul_div_cancel' hg]
    exact Dvd.dvd.mul_left h g
  · intro h
    rw [← Nat.mul_div_cancel' hg] at h
    exact hdg.dvd_of_dvd_mul_left h

theorem coprime_three_pow {k a : ℕ} (h : ¬ 3 ∣ a) : Nat.Coprime (3 ^ k) a :=
  Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h)

theorem dvd_ordA_iff {m q d : ℕ} (hm : 1 ≤ m) (hdq : Nat.Coprime d q)
    (hdg : Nat.Coprime d (Nat.gcd (m + 1) (q - 1))) :
    d ∣ ordA m q ↔ d ∣ ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i - 1) := by
  unfold ordA
  have hgP : Nat.gcd (m + 1) (q - 1) ∣ ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i - 1) :=
    (Nat.gcd_dvd_right _ _).trans ((Nat.sub_one_dvd_pow_sub_one q (m + 1)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)))
  rw [dvd_div_iff_of_coprime (Dvd.dvd.mul_left hgP _) hdg]
  exact (Nat.Coprime.pow_right _ hdq).dvd_mul_left

theorem dvd_ordBC_iff {n q d : ℕ} (hn : 1 ≤ n) (hdq : Nat.Coprime d q)
    (hdg : Nat.Coprime d (Nat.gcd 2 (q - 1))) :
    d ∣ ordBC n q ↔ d ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
  unfold ordBC
  have hgP : Nat.gcd 2 (q - 1) ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right _ _).trans ((Nat.sub_one_dvd_pow_sub_one q 2).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) (Finset.mem_Icc.2 ⟨le_rfl, hn⟩)))
  rw [dvd_div_iff_of_coprime (Dvd.dvd.mul_left hgP _) hdg]
  exact (Nat.Coprime.pow_right _ hdq).dvd_mul_left

theorem dvd_ordD_iff {n q d : ℕ} (hdq : Nat.Coprime d q)
    (hdg : Nat.Coprime d (Nat.gcd 4 (q ^ n - 1))) :
    d ∣ ordD n q ↔ d ∣ (q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) := by
  unfold ordD
  have hgP : Nat.gcd 4 (q ^ n - 1) ∣ (q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)
  rw [mul_assoc, dvd_div_iff_of_coprime (Dvd.dvd.mul_left hgP _) hdg]
  exact (Nat.Coprime.pow_right _ hdq).dvd_mul_left

theorem dvd_ordTwistedD_iff {n q d : ℕ} (hdq : Nat.Coprime d q)
    (hdg : Nat.Coprime d (Nat.gcd 4 (q ^ n + 1))) :
    d ∣ ordTwistedD n q ↔ d ∣ (q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) := by
  unfold ordTwistedD
  have hgP : Nat.gcd 4 (q ^ n + 1) ∣
      (q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)
  rw [mul_assoc, dvd_div_iff_of_coprime (Dvd.dvd.mul_left hgP _) hdg]
  exact (Nat.Coprime.pow_right _ hdq).dvd_mul_left

theorem toNat_pow_sub_neg_one_pow_even {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    (((q : ℤ) ^ i - (-1) ^ i).toNat) = q ^ i - 1 := by
  have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have : ((q : ℤ) ^ i - (-1) ^ i) = ((q ^ i - 1 : ℕ) : ℤ) := by
    rw [hi.neg_one_pow, Nat.cast_sub h1]; push_cast; ring
  rw [this, Int.toNat_natCast]

theorem toNat_pow_sub_neg_one_pow_odd {q i : ℕ} (hi : Odd i) :
    (((q : ℤ) ^ i - (-1) ^ i).toNat) = q ^ i + 1 := by
  have : ((q : ℤ) ^ i - (-1) ^ i) = ((q ^ i + 1 : ℕ) : ℤ) := by
    rw [hi.neg_one_pow]; push_cast; ring
  rw [this, Int.toNat_natCast]

theorem succ_dvd_toNat_pow_sub_neg_one_pow {q i : ℕ} (hq : 1 ≤ q) (hi : 1 ≤ i) :
    q + 1 ∣ (((q : ℤ) ^ i - (-1) ^ i).toNat) := by
  rcases Nat.even_or_odd i with he | ho
  · rw [toNat_pow_sub_neg_one_pow_even hq he]
    obtain ⟨j, rfl⟩ := he
    have h2 : q + 1 ∣ q ^ 2 - 1 := by
      have := Nat.sq_sub_sq q 1
      rw [one_pow] at this
      rw [this]
      exact dvd_mul_right _ _
    exact h2.trans (Nat.pow_sub_one_dvd_pow_sub_one q (by omega : 2 ∣ j + j))
  · rw [toNat_pow_sub_neg_one_pow_odd ho]
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 ho

theorem dvd_ordTwistedA_iff {m q d : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) (hdq : Nat.Coprime d q)
    (hdg : Nat.Coprime d (Nat.gcd (m + 1) (q + 1))) :
    d ∣ ordTwistedA m q ↔
      d ∣ ∏ i ∈ Finset.Icc 2 (m + 1), (((q : ℤ) ^ i - (-1) ^ i).toNat) := by
  unfold ordTwistedA
  have hgP : Nat.gcd (m + 1) (q + 1) ∣ ∏ i ∈ Finset.Icc 2 (m + 1), (((q : ℤ) ^ i - (-1) ^ i).toNat) :=
    (Nat.gcd_dvd_right _ _).trans ((succ_dvd_toNat_pow_sub_neg_one_pow hq (by omega : 1 ≤ m + 1)).trans
      (Finset.dvd_prod_of_mem (fun i => (((q : ℤ) ^ i - (-1) ^ i).toNat))
        (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)))
  rw [dvd_div_iff_of_coprime (Dvd.dvd.mul_left hgP _) hdg]
  exact (Nat.Coprime.pow_right _ hdq).dvd_mul_left

end Div

section SmallProd

theorem prod_two_three_four (f : ℕ → ℕ) : ∏ i ∈ ({2, 3, 4} : Finset ℕ), f i = f 2 * f 3 * f 4 := by
  simp [Finset.prod_insert, mul_assoc]

theorem prod_two_three_four_five (f : ℕ → ℕ) :
    ∏ i ∈ ({2, 3, 4, 5} : Finset ℕ), f i = f 2 * f 3 * f 4 * f 5 := by
  simp [Finset.prod_insert, mul_assoc]

theorem prod_one_two_three (f : ℕ → ℕ) : ∏ i ∈ ({1, 2, 3} : Finset ℕ), f i = f 1 * f 2 * f 3 := by
  simp [Finset.prod_insert, mul_assoc]

theorem prod_one_two_three_four (f : ℕ → ℕ) :
    ∏ i ∈ ({1, 2, 3, 4} : Finset ℕ), f i = f 1 * f 2 * f 3 * f 4 := by
  simp [Finset.prod_insert, mul_assoc]

theorem prod_two_four_six (f : ℕ → ℕ) : ∏ i ∈ ({2, 4, 6} : Finset ℕ), f i = f 2 * f 4 * f 6 := by
  simp [Finset.prod_insert, mul_assoc]

theorem prod_two_four_six_eight (f : ℕ → ℕ) :
    ∏ i ∈ ({2, 4, 6, 8} : Finset ℕ), f i = f 2 * f 4 * f 6 * f 8 := by
  simp [Finset.prod_insert, mul_assoc]

end SmallProd

section LinearOne

variable {q : ℕ}

theorem three_dvd_sub_one_of_mod_one (hq : q % 3 = 1) : 3 ∣ q - 1 := by omega

theorem three_dvd_pow_sub_one_of_mod_one (hq : q % 3 = 1) (i : ℕ) : 3 ∣ q ^ i - 1 :=
  (three_dvd_sub_one_of_mod_one hq).trans (Nat.sub_one_dvd_pow_sub_one q i)

theorem nine_dvd_pow_three_sub_one_of_mod_one (hq : q % 3 = 1) : 9 ∣ q ^ 3 - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 1 := ⟨q / 3, by omega⟩
  have : (3 * k + 1) ^ 3 = 9 * (3 * k ^ 3 + 3 * k ^ 2 + k) + 1 := by ring
  exact ⟨3 * k ^ 3 + 3 * k ^ 2 + k, by omega⟩

theorem three_pow_four_dvd_prod_one (hq : q % 3 = 1) {n : ℕ} (hn : 4 ≤ n) :
    3 ^ 4 ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
  have hsub : ({2, 3, 4} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ i - 1) hsub)
  rw [prod_two_three_four]
  have h2 := three_dvd_pow_sub_one_of_mod_one hq 2
  have h3 := nine_dvd_pow_three_sub_one_of_mod_one hq
  have h4 := three_dvd_pow_sub_one_of_mod_one hq 4
  have := mul_dvd_mul (mul_dvd_mul h2 h3) h4
  simpa using this

theorem three_pow_five_dvd_prod_one (hq : q % 3 = 1) {n : ℕ} (hn : 5 ≤ n) :
    3 ^ 5 ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
  have hsub : ({2, 3, 4, 5} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ i - 1) hsub)
  rw [prod_two_three_four_five]
  have h2 := three_dvd_pow_sub_one_of_mod_one hq 2
  have h3 := nine_dvd_pow_three_sub_one_of_mod_one hq
  have h4 := three_dvd_pow_sub_one_of_mod_one hq 4
  have h5 := three_dvd_pow_sub_one_of_mod_one hq 5
  have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul h2 h3) h4) h5
  simpa using this

theorem three_pow_four_dvd_prod_even (hq : ¬ 3 ∣ q) {k : ℕ} (hk : 3 ≤ k) :
    3 ^ 4 ∣ ∏ i ∈ Finset.Icc 1 k, (q ^ (2 * i) - 1) := by
  have hsub : ({1, 2, 3} : Finset ℕ) ⊆ Finset.Icc 1 k := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ (2 * i) - 1) hsub)
  rw [prod_one_two_three]
  have h2 := three_dvd_pow_two_mul_sub_one hq 1
  have h4 := three_dvd_pow_two_mul_sub_one hq 2
  have h6 := nine_dvd_pow_six_sub_one hq
  have := mul_dvd_mul (mul_dvd_mul h2 h4) h6
  simpa using this

theorem three_pow_five_dvd_prod_even (hq : ¬ 3 ∣ q) {k : ℕ} (hk : 4 ≤ k) :
    3 ^ 5 ∣ ∏ i ∈ Finset.Icc 1 k, (q ^ (2 * i) - 1) := by
  have hsub : ({1, 2, 3, 4} : Finset ℕ) ⊆ Finset.Icc 1 k := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ (2 * i) - 1) hsub)
  rw [prod_one_two_three_four]
  have h2 := three_dvd_pow_two_mul_sub_one hq 1
  have h4 := three_dvd_pow_two_mul_sub_one hq 2
  have h6 := nine_dvd_pow_six_sub_one hq
  have h8 := three_dvd_pow_two_mul_sub_one hq 4
  have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul h2 h4) h6) h8
  simpa using this

end LinearOne

section LinearTwo

variable {q : ℕ}

theorem not_three_dvd_pow_sub_one_of_mod_two (hq : q % 3 = 2) {i : ℕ} (hi : Odd i) :
    ¬ 3 ∣ q ^ i - 1 := by
  obtain ⟨j, rfl⟩ := hi
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have h1 : (q ^ 2) ^ j % 3 = 1 := by
    rw [Nat.pow_mod, hq2]; simp
  have h2 : q ^ (2 * j + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, h1, hq]
  intro h
  generalize q ^ (2 * j + 1) = a at h2 h
  omega

theorem three_pow_four_dvd_prod_two (hq : ¬ 3 ∣ q) {n : ℕ} (hn : 6 ≤ n) :
    3 ^ 4 ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
  have hsub : ({2, 4, 6} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ i - 1) hsub)
  rw [prod_two_four_six]
  have h2 := three_dvd_pow_two_mul_sub_one hq 1
  have h4 := three_dvd_pow_two_mul_sub_one hq 2
  have h6 := nine_dvd_pow_six_sub_one hq
  have := mul_dvd_mul (mul_dvd_mul h2 h4) h6
  simpa using this

theorem three_pow_five_dvd_prod_two (hq : ¬ 3 ∣ q) {n : ℕ} (hn : 8 ≤ n) :
    3 ^ 5 ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
  have hsub : ({2, 4, 6, 8} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ i - 1) hsub)
  rw [prod_two_four_six_eight]
  have h2 := three_dvd_pow_two_mul_sub_one hq 1
  have h4 := three_dvd_pow_two_mul_sub_one hq 2
  have h6 := nine_dvd_pow_six_sub_one hq
  have h8 := three_dvd_pow_two_mul_sub_one hq 4
  have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul h2 h4) h6) h8
  simpa using this

theorem eighty_one_dvd_prod_two_small (hq : q % 3 = 2) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (h27 : 27 ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1)) : 81 ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
  have hq3 : ¬ 3 ∣ q := by omega
  have h3 := not_three_dvd_pow_sub_one_of_mod_two hq (i := 3) (by decide)
  have h5 := not_three_dvd_pow_sub_one_of_mod_two hq (i := 5) (by decide)
  rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
  · rw [show Finset.Icc 2 4 = {2, 3, 4} by decide] at h27 ⊢
    rw [prod_two_three_four] at h27 ⊢
    have e : (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 3 - 1) := by
      ring
    rw [e] at h27 ⊢
    exact eighty_one_dvd_of_twentySeven_dvd hq3 h3 h27
  · rw [show Finset.Icc 2 5 = {2, 3, 4, 5} by decide] at h27 ⊢
    rw [prod_two_three_four_five] at h27 ⊢
    have e : (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1) =
        (q ^ 2 - 1) * (q ^ 4 - 1) * ((q ^ 3 - 1) * (q ^ 5 - 1)) := by ring
    rw [e] at h27 ⊢
    refine eighty_one_dvd_of_twentySeven_dvd hq3 ?_ h27
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact h3 h
    · exact h5 h

end LinearTwo

section Unitary

abbrev uf (q i : ℕ) : ℕ := ((q : ℤ) ^ i - (-1) ^ i).toNat

variable {q : ℕ}

theorem uf_even (hq : 1 ≤ q) {i : ℕ} (hi : Even i) : uf q i = q ^ i - 1 :=
  toNat_pow_sub_neg_one_pow_even hq hi

theorem uf_odd {i : ℕ} (hi : Odd i) : uf q i = q ^ i + 1 := toNat_pow_sub_neg_one_pow_odd hi

theorem three_dvd_pow_add_one_of_mod_two (hq : q % 3 = 2) {i : ℕ} (hi : Odd i) :
    3 ∣ q ^ i + 1 := by
  have h := Odd.nat_add_dvd_pow_add_pow q 1 hi
  rw [one_pow] at h
  exact (by omega : 3 ∣ q + 1).trans h

theorem nine_dvd_pow_three_add_one_of_mod_two (hq : q % 3 = 2) : 9 ∣ q ^ 3 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
  have : (3 * k + 2) ^ 3 + 1 = 9 * (3 * k ^ 3 + 6 * k ^ 2 + 4 * k + 1) := by ring
  rw [this]
  exact dvd_mul_right _ _

theorem not_three_dvd_pow_add_one_of_mod_one (hq : q % 3 = 1) (i : ℕ) : ¬ 3 ∣ q ^ i + 1 := by
  have h1 : q ^ i % 3 = 1 := by
    rw [Nat.pow_mod, hq]; simp
  intro h
  generalize q ^ i = a at h1 h
  omega

theorem three_pow_four_dvd_prodU_two (hq : q % 3 = 2) {n : ℕ} (hn : 4 ≤ n) :
    3 ^ 4 ∣ ∏ i ∈ Finset.Icc 2 n, uf q i := by
  have hq1 : 1 ≤ q := by omega
  have hsub : ({2, 3, 4} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => uf q i) hsub)
  rw [prod_two_three_four, uf_even hq1 (by decide), uf_odd (by decide), uf_even hq1 (by decide)]
  have h2 := three_dvd_pow_two_mul_sub_one (by omega : ¬ 3 ∣ q) 1
  have h3 := nine_dvd_pow_three_add_one_of_mod_two hq
  have h4 := three_dvd_pow_two_mul_sub_one (by omega : ¬ 3 ∣ q) 2
  have := mul_dvd_mul (mul_dvd_mul h2 h3) h4
  simpa using this

theorem three_pow_five_dvd_prodU_two (hq : q % 3 = 2) {n : ℕ} (hn : 5 ≤ n) :
    3 ^ 5 ∣ ∏ i ∈ Finset.Icc 2 n, uf q i := by
  have hq1 : 1 ≤ q := by omega
  have hsub : ({2, 3, 4, 5} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => uf q i) hsub)
  rw [prod_two_three_four_five, uf_even hq1 (by decide), uf_odd (by decide),
    uf_even hq1 (by decide), uf_odd (by decide)]
  have h2 := three_dvd_pow_two_mul_sub_one (by omega : ¬ 3 ∣ q) 1
  have h3 := nine_dvd_pow_three_add_one_of_mod_two hq
  have h4 := three_dvd_pow_two_mul_sub_one (by omega : ¬ 3 ∣ q) 2
  have h5 := three_dvd_pow_add_one_of_mod_two hq (i := 5) (by decide)
  have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul h2 h3) h4) h5
  simpa using this

theorem three_pow_four_dvd_prodU_one (hq : q % 3 = 1) {n : ℕ} (hn : 6 ≤ n) :
    3 ^ 4 ∣ ∏ i ∈ Finset.Icc 2 n, uf q i := by
  have hq1 : 1 ≤ q := by omega
  have hsub : ({2, 4, 6} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => uf q i) hsub)
  rw [prod_two_four_six, uf_even hq1 (by decide), uf_even hq1 (by decide),
    uf_even hq1 (by decide)]
  have h2 := three_dvd_pow_two_mul_sub_one (by omega : ¬ 3 ∣ q) 1
  have h4 := three_dvd_pow_two_mul_sub_one (by omega : ¬ 3 ∣ q) 2
  have h6 := nine_dvd_pow_six_sub_one (by omega : ¬ 3 ∣ q)
  have := mul_dvd_mul (mul_dvd_mul h2 h4) h6
  simpa using this

theorem three_pow_five_dvd_prodU_one (hq : q % 3 = 1) {n : ℕ} (hn : 8 ≤ n) :
    3 ^ 5 ∣ ∏ i ∈ Finset.Icc 2 n, uf q i := by
  have hq1 : 1 ≤ q := by omega
  have hsub : ({2, 4, 6, 8} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => uf q i) hsub)
  rw [prod_two_four_six_eight, uf_even hq1 (by decide), uf_even hq1 (by decide),
    uf_even hq1 (by decide), uf_even hq1 (by decide)]
  have h2 := three_dvd_pow_two_mul_sub_one (by omega : ¬ 3 ∣ q) 1
  have h4 := three_dvd_pow_two_mul_sub_one (by omega : ¬ 3 ∣ q) 2
  have h6 := nine_dvd_pow_six_sub_one (by omega : ¬ 3 ∣ q)
  have h8 := three_dvd_pow_two_mul_sub_one (by omega : ¬ 3 ∣ q) 4
  have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul h2 h4) h6) h8
  simpa using this

theorem eighty_one_dvd_prodU_one_small (hq : q % 3 = 1) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (h27 : 27 ∣ ∏ i ∈ Finset.Icc 2 n, uf q i) : 81 ∣ ∏ i ∈ Finset.Icc 2 n, uf q i := by
  have hq1 : 1 ≤ q := by omega
  have hq3 : ¬ 3 ∣ q := by omega
  have h3 := not_three_dvd_pow_add_one_of_mod_one hq 3
  have h5 := not_three_dvd_pow_add_one_of_mod_one hq 5
  rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
  · rw [show Finset.Icc 2 4 = {2, 3, 4} by decide] at h27 ⊢
    rw [prod_two_three_four, uf_even hq1 (by decide), uf_odd (by decide),
      uf_even hq1 (by decide)] at h27 ⊢
    have e : (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 3 + 1) := by
      ring
    rw [e] at h27 ⊢
    exact eighty_one_dvd_of_twentySeven_dvd hq3 h3 h27
  · rw [show Finset.Icc 2 5 = {2, 3, 4, 5} by decide] at h27 ⊢
    rw [prod_two_three_four_five, uf_even hq1 (by decide), uf_odd (by decide),
      uf_even hq1 (by decide), uf_odd (by decide)] at h27 ⊢
    have e : (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1) =
        (q ^ 2 - 1) * (q ^ 4 - 1) * ((q ^ 3 + 1) * (q ^ 5 + 1)) := by ring
    rw [e] at h27 ⊢
    refine eighty_one_dvd_of_twentySeven_dvd hq3 ?_ h27
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact h3 h
    · exact h5 h

end Unitary

section G2

variable {q : ℕ}

theorem three_pow_five_dvd_ordG2 (hq : ¬ 3 ∣ q) (h : 3 ^ 4 ∣ ordG2 q) : 3 ^ 5 ∣ ordG2 q := by
  obtain ⟨s, hs⟩ := exists_sq_eq hq
  have h6 : q ^ 6 = 27 * s ^ 3 + 27 * s ^ 2 + 9 * s + 1 := by
    rw [show q ^ 6 = (q ^ 2) ^ 3 by ring, hs]; ring
  have e6 : q ^ 6 - 1 = 9 * s * (3 * s ^ 2 + 3 * s + 1) := by
    have : q ^ 6 = 9 * s * (3 * s ^ 2 + 3 * s + 1) + 1 := by rw [h6]; ring
    omega
  have e2 : q ^ 2 - 1 = 3 * s := by omega
  have hN : ordG2 q = 27 * (s ^ 2 * (3 * s ^ 2 + 3 * s + 1) * q ^ 6) := by
    unfold ordG2
    rw [e6, e2]
    ring
  rw [hN] at h ⊢
  have h3 : 3 ∣ s ^ 2 * (3 * s ^ 2 + 3 * s + 1) * q ^ 6 := by
    have : 27 * 3 ∣ 27 * (s ^ 2 * (3 * s ^ 2 + 3 * s + 1) * q ^ 6) := by simpa using h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h3 | h3
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h3 | h3
    · have hs3 : 3 ∣ s := Nat.prime_three.dvd_of_dvd_pow h3
      obtain ⟨t, rfl⟩ := hs3
      exact ⟨t ^ 2 * (3 * (3 * t) ^ 2 + 3 * (3 * t) + 1) * q ^ 6, by ring⟩
    · omega
  · exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) hq

end G2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.CrossArith

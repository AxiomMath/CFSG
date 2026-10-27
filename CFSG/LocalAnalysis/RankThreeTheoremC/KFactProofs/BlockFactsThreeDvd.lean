module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open

theorem three_dvd_two_pow_sq_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  have := Nat.sub_dvd_pow_sub_pow 4 1 f
  rw [one_pow] at this
  rw [← pow_mul, mul_comm, pow_mul]
  simpa using this

theorem three_dvd_div_of_mul_dvd {N g : ℕ} (h : 3 * g ∣ N) : 3 ∣ N / g := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  obtain ⟨m, rfl⟩ := h
  rw [show 3 * g * m = g * (3 * m) by ring, Nat.mul_div_cancel_left _ hg]
  exact dvd_mul_right 3 m

theorem succ_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  rcases q with _ | r
  · simp
  · exact ⟨r, by
      have : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
      omega⟩

theorem pred_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow q 1 2

theorem odd_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one

theorem three_dvd_ordA {k f : ℕ} (hk : 1 ≤ k) : 3 ∣ ordA k (2 ^ f) := by
  unfold ordA
  refine three_dvd_div_of_mul_dvd (Dvd.dvd.mul_left ?_ _)
  set q := 2 ^ f with hq
  have h2 : (q ^ 2 - 1) ∣ ∏ i ∈ Finset.Icc 2 (k + 1), (q ^ i - 1) :=
    Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have h3sq : 3 ∣ q ^ 2 - 1 := three_dvd_two_pow_sq_sub_one f
  have hgq : Nat.gcd (k + 1) (q - 1) ∣ q ^ 2 - 1 :=
    (Nat.gcd_dvd_right _ _).trans (pred_dvd_sq_sub_one q)
  by_cases h3g : 3 ∣ Nat.gcd (k + 1) (q - 1)
  · have h3q : 3 ∣ q - 1 := h3g.trans (Nat.gcd_dvd_right _ _)
    have h3k : 3 ∣ k + 1 := h3g.trans (Nat.gcd_dvd_left _ _)
    have hk2 : 2 ≤ k := by omega
    have h3cube : 3 ∣ q ^ 3 - 1 := h3q.trans (by simpa using Nat.sub_dvd_pow_sub_pow q 1 3)
    have hpair : (q ^ 2 - 1) * (q ^ 3 - 1) ∣ ∏ i ∈ Finset.Icc 2 (k + 1), (q ^ i - 1) := by
      have := Finset.prod_dvd_prod_of_subset ({2, 3} : Finset ℕ) (Finset.Icc 2 (k + 1))
        (fun i => q ^ i - 1) (by intro i hi; simp only [Finset.mem_insert,
          Finset.mem_singleton] at hi; simp only [Finset.mem_Icc]; omega)
      rwa [Finset.prod_pair (by norm_num)] at this
    exact (mul_dvd_mul h3cube hgq).trans (by rw [mul_comm]; exact hpair)
  · have hcop : Nat.Coprime 3 (Nat.gcd (k + 1) (q - 1)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3g
    exact (hcop.mul_dvd_of_dvd_of_dvd h3sq hgq).trans h2

theorem toNat_sq_sub_neg_one_sq (q : ℕ) (hq : 1 ≤ q) :
    (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := by
  have h : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
    push_cast
    ring
  rw [h, Int.toNat_natCast]

theorem toNat_cube_sub_neg_one_cube (q : ℕ) :
    (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) = q ^ 3 + 1 := by
  have h : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h, Int.toNat_natCast]

theorem three_dvd_ordTwistedA {k f : ℕ} (hk : 1 ≤ k) : 3 ∣ ordTwistedA k (2 ^ f) := by
  unfold ordTwistedA
  refine three_dvd_div_of_mul_dvd (Dvd.dvd.mul_left ?_ _)
  set q := 2 ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have h2 : (q ^ 2 - 1) ∣ ∏ i ∈ Finset.Icc 2 (k + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
    have := Finset.dvd_prod_of_mem (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
      (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩ : 2 ∈ Finset.Icc 2 (k + 1))
    rwa [toNat_sq_sub_neg_one_sq q hq1] at this
  have h3sq : 3 ∣ q ^ 2 - 1 := three_dvd_two_pow_sq_sub_one f
  have hgq : Nat.gcd (k + 1) (q + 1) ∣ q ^ 2 - 1 :=
    (Nat.gcd_dvd_right _ _).trans (succ_dvd_sq_sub_one q)
  by_cases h3g : 3 ∣ Nat.gcd (k + 1) (q + 1)
  · have h3q : 3 ∣ q + 1 := h3g.trans (Nat.gcd_dvd_right _ _)
    have h3k : 3 ∣ k + 1 := h3g.trans (Nat.gcd_dvd_left _ _)
    have hk2 : 2 ≤ k := by omega
    have h3cube : 3 ∣ q ^ 3 + 1 :=
      h3q.trans (by simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3))
    have hpair : (q ^ 2 - 1) * (q ^ 3 + 1) ∣
        ∏ i ∈ Finset.Icc 2 (k + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
      have := Finset.prod_dvd_prod_of_subset ({2, 3} : Finset ℕ) (Finset.Icc 2 (k + 1))
        (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) (by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          simp only [Finset.mem_Icc]
          omega)
      rwa [Finset.prod_pair (by norm_num), toNat_sq_sub_neg_one_sq q hq1,
        toNat_cube_sub_neg_one_cube] at this
    exact (mul_dvd_mul h3cube hgq).trans (by rw [mul_comm]; exact hpair)
  · have hcop : Nat.Coprime 3 (Nat.gcd (k + 1) (q + 1)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3g
    exact (hcop.mul_dvd_of_dvd_of_dvd h3sq hgq).trans h2

theorem three_dvd_ordBC {m f : ℕ} (hm : 1 ≤ m) : 3 ∣ ordBC m (2 ^ f) := by
  unfold ordBC
  refine three_dvd_div_of_mul_dvd (Dvd.dvd.mul_left ?_ _)
  have h1 : ((2 ^ f) ^ (2 * 1) - 1) ∣ ∏ i ∈ Finset.Icc 1 m, ((2 ^ f) ^ (2 * i) - 1) :=
    Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) (Finset.mem_Icc.2 ⟨le_rfl, hm⟩)
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · rw [Finset.prod_eq_zero (i := 1) (Finset.mem_Icc.2 ⟨le_rfl, hm⟩) (by simp)]
    exact dvd_zero _
  · have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf)
    rw [hg, mul_one]
    have h3 : 3 ∣ (2 ^ f) ^ (2 * 1) - 1 := by simpa using three_dvd_two_pow_sq_sub_one f
    exact h3.trans h1

theorem three_dvd_ordD {m f : ℕ} (hm : 2 ≤ m) : 3 ∣ ordD m (2 ^ f) := by
  unfold ordD
  refine three_dvd_div_of_mul_dvd (Dvd.dvd.mul_left ?_ _)
  have h1 : ((2 ^ f) ^ (2 * 1) - 1) ∣ ∏ i ∈ Finset.Icc 1 (m - 1), ((2 ^ f) ^ (2 * i) - 1) :=
    Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1)
      (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · rw [Finset.prod_eq_zero (i := 1) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) (by simp)]
    exact dvd_zero _
  · have hodd : Odd ((2 ^ f) ^ m - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow _ _ (Nat.two_pow_pos f))
        ((Nat.even_pow' (by omega)).mpr ((Nat.even_pow' (by omega)).mpr even_two)) odd_one
    have hg : Nat.gcd 4 ((2 ^ f) ^ m - 1) = 1 :=
      (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) : Nat.Coprime (2 ^ 2) _)
    have h3 : 3 ∣ (2 ^ f) ^ (2 * 1) - 1 := by simpa using three_dvd_two_pow_sq_sub_one f
    rw [hg, mul_one]
    exact h3.trans h1

theorem three_dvd_ordTwistedD {m f : ℕ} (hm : 2 ≤ m) : 3 ∣ ordTwistedD m (2 ^ f) := by
  unfold ordTwistedD
  refine three_dvd_div_of_mul_dvd (Dvd.dvd.mul_left ?_ _)
  have h1 : ((2 ^ f) ^ (2 * 1) - 1) ∣ ∏ i ∈ Finset.Icc 1 (m - 1), ((2 ^ f) ^ (2 * i) - 1) :=
    Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1)
      (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · rw [Finset.prod_eq_zero (i := 1) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) (by simp)]
    exact dvd_zero _
  · have hodd : Odd ((2 ^ f) ^ m + 1) :=
      Even.add_one ((Nat.even_pow' (by omega)).mpr ((Nat.even_pow' (by omega)).mpr even_two))
    have hg : Nat.gcd 4 ((2 ^ f) ^ m + 1) = 1 :=
      (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) : Nat.Coprime (2 ^ 2) _)
    have h3 : 3 ∣ (2 ^ f) ^ (2 * 1) - 1 := by simpa using three_dvd_two_pow_sq_sub_one f
    rw [hg, mul_one]
    exact h3.trans h1

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

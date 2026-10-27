module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpOrderL2
public import Mathlib.Tactic.IntervalCases

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG.ComponentClassification.CatLeafProof.X10Sp

theorem cofactor_psp4_lt {q : ℕ} (hq : 2 ≤ q) : (q ^ 2 - 1) * (q ^ 4 - 1) < (q ^ 4) ^ 2 - 1 := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h8 : 1 ≤ (q ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h4, h8]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hq2 : (4 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
  have hq6 : (0 : ℤ) < (q : ℤ) ^ 6 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hq2 hq6.le]

theorem false_of_card_psl2_psp4 {p f e N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (he : 1 ≤ e)
    (h1 : N * Nat.gcd 2 (p ^ e - 1) =
      (p ^ e) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ e) ^ i - 1))
    (h2 : N * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1))
    (hv : 2 * (2 - 1) / 2 * e = 2 ^ 2 * f) : False := by
  obtain ⟨hq3, hg⟩ := three_le_and_gcd hp hp2 hf
  obtain ⟨-, hg'⟩ := three_le_and_gcd hp hp2 he
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR, hg'] at h1
  rw [prod_Icc_one_two, hg] at h2
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  have hr : p ^ e = (p ^ f) ^ 4 := by
    rw [← pow_mul]
    congr 1
    norm_num at hv
    omega
  rw [Finset.Icc_self, Finset.prod_singleton, hr] at hM
  have := cofactor_psp4_lt (q := p ^ f) (by omega)
  omega

theorem false_of_psl4_psp4_eq {s g : ℤ} (hs : 3 ≤ s) (hg : g = 1 ∨ g = 2 ∨ g = 4)
    (h : (s ^ 4 - 1) * ((s ^ 6 - 1) * (s ^ 8 - 1)) * 2 = (s ^ 6 - 1) * (s ^ 12 - 1) * g) :
    False := by
  have h4 : 81 ≤ s ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hs 4
    norm_num at this
    exact this
  have h6 : 0 < s ^ 6 - 1 := by
    have := pow_le_pow_left₀ (by norm_num) hs 6
    norm_num at this
    linarith
  have h8 : 0 < s ^ 8 := by positivity
  have h48 : 81 * s ^ 4 ≤ s ^ 8 := by
    have := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℤ) ≤ s ^ 4)
    linarith [show s ^ 8 = s ^ 4 * s ^ 4 by ring]
  rcases hg with rfl | rfl | rfl
  · have hA : 0 < s ^ 12 - 2 * s ^ 8 - 2 * s ^ 4 + 3 := by
      nlinarith [mul_pos h8 (by linarith : (0 : ℤ) < s ^ 4 - 3)]
    nlinarith [mul_pos h6 hA]
  · have hB : 0 < 2 * s ^ 8 + 2 * s ^ 4 - 4 := by linarith
    nlinarith [mul_pos h6 hB]
  · have hC : 0 < 2 * s ^ 12 + 2 * s ^ 8 + 2 * s ^ 4 - 6 := by
      nlinarith [mul_pos h8 (by linarith : (0 : ℤ) < s ^ 4)]
    nlinarith [mul_pos h6 hC]

theorem eq_one_or_two_or_four_of_dvd {g : ℕ} (hg : g ∣ 4) : g = 1 ∨ g = 2 ∨ g = 4 := by
  have hg4 : g ≤ 4 := Nat.le_of_dvd (by norm_num) hg
  interval_cases g <;> omega

theorem false_of_card_psl4_psp4 {p f e N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h1 : N * Nat.gcd 4 (p ^ e - 1) =
      (p ^ e) ^ (4 * (4 - 1) / 2) * ∏ i ∈ Finset.Icc 2 4, ((p ^ e) ^ i - 1))
    (h2 : N * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1))
    (hv : 4 * (4 - 1) / 2 * e = 2 ^ 2 * f) : False := by
  obtain ⟨-, hg⟩ := three_le_and_gcd hp hp2 hf
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR] at h1
  rw [prod_Icc_one_two, hg] at h2
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  norm_num at hv
  obtain ⟨c, rfl⟩ : ∃ c, e = 2 * c := ⟨e / 2, by omega⟩
  obtain rfl : f = 3 * c := by omega
  have hs := (three_le_and_gcd hp hp2 (by omega : 1 ≤ c)).1
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num), pow_mul' p 2 c, pow_mul' p 3 c] at hM
  have hgc := eq_one_or_two_or_four_of_dvd (Nat.gcd_dvd_left 4 ((p ^ c) ^ 2 - 1))
  set g := Nat.gcd 4 ((p ^ c) ^ 2 - 1)
  set s := p ^ c
  have hs0 : 0 < s := by omega
  have e2 : 1 ≤ (s ^ 2) ^ 2 := Nat.one_le_pow _ _ (pow_pos hs0 _)
  have e3 : 1 ≤ (s ^ 2) ^ 3 := Nat.one_le_pow _ _ (pow_pos hs0 _)
  have e4 : 1 ≤ (s ^ 2) ^ 4 := Nat.one_le_pow _ _ (pow_pos hs0 _)
  have e6 : 1 ≤ (s ^ 3) ^ 2 := Nat.one_le_pow _ _ (pow_pos hs0 _)
  have e12 : 1 ≤ (s ^ 3) ^ 4 := Nat.one_le_pow _ _ (pow_pos hs0 _)
  zify [e2, e3, e4, e6, e12] at hM
  exact false_of_psl4_psp4_eq (s := (s : ℤ)) (g := (g : ℤ)) (by exact_mod_cast hs)
    (by rcases hgc with h | h | h <;> simp [h]) (by linear_combination hM)

theorem false_of_psu4_psp4_eq {s g : ℤ} (hs : 3 ≤ s) (hg : g = 1 ∨ g = 2 ∨ g = 4)
    (h : (s ^ 4 - 1) * ((s ^ 6 + 1) * (s ^ 8 - 1)) * 2 = (s ^ 6 - 1) * (s ^ 12 - 1) * g) :
    False := by
  have h2 : 9 ≤ s ^ 2 := by nlinarith
  have h4 : 81 ≤ s ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hs 4
    norm_num at this
    exact this
  have h6 : 729 ≤ s ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num) hs 6
    norm_num at this
    exact this
  have h6p : 0 < s ^ 6 + 1 := by positivity
  have h8 : 0 < s ^ 8 := by positivity
  have h4p : 0 < s ^ 4 := by positivity
  rcases hg with rfl | rfl | rfl
  · have hA : 0 < s ^ 12 - 2 * s ^ 8 + 2 * s ^ 6 - 2 * s ^ 4 + 1 := by
      nlinarith [mul_pos h8 (by linarith : (0 : ℤ) < s ^ 4 - 2),
        mul_pos h4p (by linarith : (0 : ℤ) < s ^ 2 - 1)]
    nlinarith [mul_pos h6p hA]
  · have hB : 0 < 2 * s ^ 4 * (s ^ 2 - 1) ^ 2 := by
      have : 0 < s ^ 2 - 1 := by linarith
      positivity
    nlinarith [mul_pos h6p hB]
  · have hC : 0 < 2 * s ^ 12 + 2 * s ^ 8 - 8 * s ^ 6 + 2 * s ^ 4 + 2 := by
      nlinarith [mul_pos (by linarith : (0 : ℤ) < s ^ 6) (by linarith : (0 : ℤ) < s ^ 6 - 4)]
    nlinarith [mul_pos h6p hC]

theorem false_of_card_psu4_psp4 {p f e N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h1 : N * Nat.gcd 4 (p ^ e + 1) = (p ^ e) ^ (4 * (4 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 4, (if Even i then (p ^ e) ^ i - 1 else (p ^ e) ^ i + 1))
    (h2 : N * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1))
    (hv : 4 * (4 - 1) / 2 * e = 2 ^ 2 * f) : False := by
  obtain ⟨-, hg⟩ := three_le_and_gcd hp hp2 hf
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR] at h1
  rw [prod_Icc_one_two, hg] at h2
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  norm_num at hv
  obtain ⟨c, rfl⟩ : ∃ c, e = 2 * c := ⟨e / 2, by omega⟩
  obtain rfl : f = 3 * c := by omega
  have hs := (three_le_and_gcd hp hp2 (by omega : 1 ≤ c)).1
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num), pow_mul' p 2 c, pow_mul' p 3 c] at hM
  simp only [show Even 2 by decide, show ¬ Even 3 by decide, show Even 4 by decide,
    ↓reduceIte] at hM
  have hgc := eq_one_or_two_or_four_of_dvd (Nat.gcd_dvd_left 4 ((p ^ c) ^ 2 + 1))
  set g := Nat.gcd 4 ((p ^ c) ^ 2 + 1)
  set s := p ^ c
  have hs0 : 0 < s := by omega
  have e2 : 1 ≤ (s ^ 2) ^ 2 := Nat.one_le_pow _ _ (pow_pos hs0 _)
  have e4 : 1 ≤ (s ^ 2) ^ 4 := Nat.one_le_pow _ _ (pow_pos hs0 _)
  have e6 : 1 ≤ (s ^ 3) ^ 2 := Nat.one_le_pow _ _ (pow_pos hs0 _)
  have e12 : 1 ≤ (s ^ 3) ^ 4 := Nat.one_le_pow _ _ (pow_pos hs0 _)
  zify [e2, e4, e6, e12] at hM
  exact false_of_psu4_psp4_eq (s := (s : ℤ)) (g := (g : ℤ)) (by exact_mod_cast hs)
    (by rcases hgc with h | h | h <;> simp [h]) (by linear_combination hM)

theorem false_of_card_pomegaOdd_psp4 {p f e m N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (he : 1 ≤ e) (hm : 3 ≤ m)
    (h1 : N * 2 = (p ^ e) ^ (m ^ 2) * ∏ i ∈ Finset.Icc 1 m, ((p ^ e) ^ (2 * i) - 1))
    (h2 : N * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1))
    (hv : m ^ 2 * e = 2 ^ 2 * f) : False :=
  false_of_card_psp_psp4 hp hp2 hf he hm (by rw [(three_le_and_gcd hp hp2 he).2]; exact h1) h2
    hv

theorem false_of_even_orthogonal_bound {q r m M g c : ℕ} (hq : 3 ≤ q) (hr : 3 ≤ r) (hm : 4 ≤ m)
    (hc : c ≤ 2) (hg : 1 ≤ g) (hM : M * 2 = (q ^ 2 - 1) * (q ^ 4 - 1) * g)
    (hMb : M ≤ c * r ^ (m ^ 2)) (h12 : q ^ 12 = r ^ (3 * (m * (m - 1)))) : False := by
  have hlow := psp4_sq_lower hq
  set M₂ := (q ^ 2 - 1) * (q ^ 4 - 1)
  have hM₂ : M₂ ≤ 2 * c * r ^ (m ^ 2) := by
    calc M₂ ≤ M₂ * g := Nat.le_mul_of_pos_right _ hg
      _ = M * 2 := hM.symm
      _ ≤ c * r ^ (m ^ 2) * 2 := Nat.mul_le_mul_right _ hMb
      _ = 2 * c * r ^ (m ^ 2) := by ring
  have hsq : M₂ ^ 2 ≤ 16 * r ^ (2 * m ^ 2) := by
    calc M₂ ^ 2 ≤ (2 * c * r ^ (m ^ 2)) ^ 2 := Nat.pow_le_pow_left hM₂ 2
      _ ≤ (4 * r ^ (m ^ 2)) ^ 2 :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega)) 2
      _ = 16 * r ^ (2 * m ^ 2) := by ring
  have hE : 2 * m ^ 2 + 4 ≤ 3 * (m * (m - 1)) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega]
    nlinarith
  have hbig : 81 * r ^ (2 * m ^ 2) ≤ q ^ 12 := by
    rw [h12]
    calc 81 * r ^ (2 * m ^ 2) ≤ r ^ 4 * r ^ (2 * m ^ 2) :=
          Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_left hr 4)
      _ = r ^ (2 * m ^ 2 + 4) := by ring
      _ ≤ r ^ (3 * (m * (m - 1))) := Nat.pow_le_pow_right (by omega) hE
  have hX : 1 ≤ r ^ (2 * m ^ 2) := Nat.one_le_pow _ _ (by omega)
  omega

theorem false_of_card_pomegaPlus_psp4 {p f e m N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (he : 1 ≤ e) (hm : 4 ≤ m)
    (h1 : N * Nat.gcd 4 ((p ^ e) ^ m - 1) = (p ^ e) ^ (m * (m - 1)) * ((p ^ e) ^ m - 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), ((p ^ e) ^ (2 * i) - 1))
    (h2 : N * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1))
    (hv : m * (m - 1) * e = 2 ^ 2 * f) : False := by
  obtain ⟨hq3, hg⟩ := three_le_and_gcd hp hp2 hf
  obtain ⟨hr3, -⟩ := three_le_and_gcd hp hp2 he
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR, mul_assoc] at h1
  rw [prod_Icc_one_two, hg] at h2
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  set r := p ^ e
  have hP := prod_Icc_pow_two_mul_sub_one_le r (m - 1)
  have hMb : (r ^ m - 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (r ^ (2 * i) - 1) ≤ 1 * r ^ (m ^ 2) := by
    calc (r ^ m - 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (r ^ (2 * i) - 1) ≤
        r ^ m * r ^ ((m - 1) * (m - 1 + 1)) := Nat.mul_le_mul (Nat.sub_le _ _) hP
      _ = 1 * r ^ (m ^ 2) := by
        rw [one_mul, ← pow_add]
        congr 1
        rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [Nat.add_sub_cancel]
        ring
  have h12 : (p ^ f) ^ 12 = r ^ (3 * (m * (m - 1))) := by
    rw [pow_mul', hR]
    ring
  exact false_of_even_orthogonal_bound hq3 hr3 hm (by norm_num)
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) hM hMb h12

theorem false_of_card_pomegaMinus_psp4 {p f e m N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (he : 1 ≤ e) (hm : 4 ≤ m)
    (h1 : N * Nat.gcd 4 ((p ^ e) ^ m + 1) = (p ^ e) ^ (m * (m - 1)) * ((p ^ e) ^ m + 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), ((p ^ e) ^ (2 * i) - 1))
    (h2 : N * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1))
    (hv : m * (m - 1) * e = 2 ^ 2 * f) : False := by
  obtain ⟨hq3, hg⟩ := three_le_and_gcd hp hp2 hf
  obtain ⟨hr3, -⟩ := three_le_and_gcd hp hp2 he
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR, mul_assoc] at h1
  rw [prod_Icc_one_two, hg] at h2
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  set r := p ^ e
  have hP := prod_Icc_pow_two_mul_sub_one_le r (m - 1)
  have hrm : r ^ m + 1 ≤ 2 * r ^ m := by
    have : 1 ≤ r ^ m := Nat.one_le_pow _ _ (by omega)
    omega
  have hMb : (r ^ m + 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (r ^ (2 * i) - 1) ≤ 2 * r ^ (m ^ 2) := by
    calc (r ^ m + 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (r ^ (2 * i) - 1) ≤
        (2 * r ^ m) * r ^ ((m - 1) * (m - 1 + 1)) := Nat.mul_le_mul hrm hP
      _ = 2 * r ^ (m ^ 2) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [Nat.add_sub_cancel]
        ring
  have h12 : (p ^ f) ^ 12 = r ^ (3 * (m * (m - 1))) := by
    rw [pow_mul', hR]
    ring
  exact false_of_even_orthogonal_bound hq3 hr3 hm le_rfl
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) hM hMb h12

theorem sum_add_one_le {n : ℕ} (hn : 3 ≤ n) :
    ∑ i ∈ Finset.Icc 2 n, i + 1 ≤ 2 * (n * (n - 1) / 2) := by
  have hS := two_mul_sum_Icc_two (n := n) (by omega)
  have hT : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  have key : n * (n + 1) ≤ 2 * (n * (n - 1)) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega]
    nlinarith
  omega

theorem false_of_card_psl_l2 {p f e n N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (he : 1 ≤ e) (hn : 3 ≤ n)
    (h1 : N * Nat.gcd n (p ^ e - 1) =
      (p ^ e) ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, ((p ^ e) ^ i - 1))
    (h2 : N * Nat.gcd 2 (p ^ (2 * f) - 1) =
      (p ^ (2 * f)) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ (2 * f)) ^ i - 1))
    (hv : n * (n - 1) / 2 * e = 2 * (2 - 1) / 2 * (2 * f)) : False := by
  obtain ⟨hk3, -⟩ := three_le_and_gcd hp hp2 he
  obtain ⟨-, hg⟩ := three_le_and_gcd hp hp2 (by omega : 1 ≤ 2 * f)
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR] at h1
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  have hv' : n * (n - 1) / 2 * e = 2 * f := by simpa using hv
  rw [hg, Finset.Icc_self, Finset.prod_singleton, pow_two_mul_eq hv'] at hM
  have hE := sum_add_one_le hn
  have hS2 : 2 ≤ ∑ i ∈ Finset.Icc 2 n, i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le i) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have hP := prod_Icc_pow_sub_one_le (p ^ e) n
  set k := p ^ e
  set T := n * (n - 1) / 2
  set S := ∑ i ∈ Finset.Icc 2 n, i
  have hg1 : 1 ≤ Nat.gcd n (k - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hle := Nat.le_mul_of_pos_right ((k ^ T) ^ 2 - 1) hg1
  have hbig : 3 * k ^ S ≤ (k ^ T) ^ 2 := by
    calc 3 * k ^ S ≤ k * k ^ S := Nat.mul_le_mul_right _ hk3
      _ = k ^ (S + 1) := by ring
      _ ≤ k ^ (2 * T) := Nat.pow_le_pow_right (by omega) hE
      _ = (k ^ T) ^ 2 := by ring
  have hX : 3 ≤ k ^ S := hk3.trans (Nat.le_self_pow (by omega) k)
  omega

theorem false_of_card_psu_l2 {p f e n N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (he : 1 ≤ e) (hn : 3 ≤ n)
    (h1 : N * Nat.gcd n (p ^ e + 1) = (p ^ e) ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (if Even i then (p ^ e) ^ i - 1 else (p ^ e) ^ i + 1))
    (h2 : N * Nat.gcd 2 (p ^ (2 * f) - 1) =
      (p ^ (2 * f)) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ (2 * f)) ^ i - 1))
    (hv : n * (n - 1) / 2 * e = 2 * (2 - 1) / 2 * (2 * f)) : False := by
  obtain ⟨hk3, -⟩ := three_le_and_gcd hp hp2 he
  obtain ⟨-, hg⟩ := three_le_and_gcd hp hp2 (by omega : 1 ≤ 2 * f)
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR] at h1
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  have hv' : n * (n - 1) / 2 * e = 2 * f := by simpa using hv
  rw [hg, Finset.Icc_self, Finset.prod_singleton, pow_two_mul_eq hv'] at hM
  have hE := sum_add_one_le hn
  have hS2 : 2 ≤ ∑ i ∈ Finset.Icc 2 n, i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le i) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have hP := (Nat.mul_le_mul_left 4 (prod_unitary_le_prod (p ^ e) n)).trans
    (four_mul_prod_Icc_pow_add_one_le hk3 (by omega : 2 ≤ n))
  set k := p ^ e
  set T := n * (n - 1) / 2
  set S := ∑ i ∈ Finset.Icc 2 n, i
  have hg1 : 1 ≤ Nat.gcd n (k + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hle := Nat.le_mul_of_pos_right ((k ^ T) ^ 2 - 1) hg1
  have hbig : 3 * k ^ S ≤ (k ^ T) ^ 2 := by
    calc 3 * k ^ S ≤ k * k ^ S := Nat.mul_le_mul_right _ hk3
      _ = k ^ (S + 1) := by ring
      _ ≤ k ^ (2 * T) := Nat.pow_le_pow_right (by omega) hE
      _ = (k ^ T) ^ 2 := by ring
  have hX : 3 ≤ k ^ S := hk3.trans (Nat.le_self_pow (by omega) k)
  omega

end CFSG.ComponentClassification.CatLeafProof.X10Lin

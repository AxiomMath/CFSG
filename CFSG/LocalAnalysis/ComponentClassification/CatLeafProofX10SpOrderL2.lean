module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpOrder

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Sp

theorem pow_two_mul_eq {p f e m : ℕ} (h : m * e = 2 * f) : p ^ (2 * f) = (p ^ e) ^ m := by
  rw [← pow_mul, ← h, mul_comm]

theorem false_of_card_psl4_l2 {p f f' N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hf' : 1 ≤ f')
    (h1 : N * Nat.gcd 4 (p ^ f' - 1) =
      (p ^ f') ^ (4 * (4 - 1) / 2) * ∏ i ∈ Finset.Icc 2 4, ((p ^ f') ^ i - 1))
    (h2 : N * Nat.gcd 2 (p ^ (2 * f) - 1) =
      (p ^ (2 * f)) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ (2 * f)) ^ i - 1))
    (hv : 4 * (4 - 1) / 2 * f' = 2 * (2 - 1) / 2 * (2 * f)) : False := by
  obtain ⟨hk3, -⟩ := three_le_and_gcd hp hp2 hf'
  obtain ⟨-, hg⟩ := three_le_and_gcd hp hp2 (by omega : 1 ≤ 2 * f)
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR] at h1
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  rw [hg, Finset.Icc_self, Finset.prod_singleton, pow_two_mul_eq (m := 6) (e := f') (by omega)]
    at hM
  set k := p ^ f'
  have hg1 : 1 ≤ Nat.gcd 4 (k - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hP := prod_Icc_pow_sub_one_le k 4
  rw [show ∑ i ∈ Finset.Icc 2 4, i = 9 by decide] at hP
  have hle := Nat.le_mul_of_pos_right ((k ^ 6) ^ 2 - 1) hg1
  have h12 : (k ^ 6) ^ 2 = k ^ 3 * k ^ 9 := by ring
  have h27 : 27 * k ^ 9 ≤ k ^ 3 * k ^ 9 :=
    Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_left hk3 3)
  have hX : 1 ≤ k ^ 9 := Nat.one_le_pow _ _ (by omega)
  omega

theorem false_of_card_psu4_l2 {p f f' N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hf' : 1 ≤ f')
    (h1 : N * Nat.gcd 4 (p ^ f' + 1) = (p ^ f') ^ (4 * (4 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 4, (if Even i then (p ^ f') ^ i - 1 else (p ^ f') ^ i + 1))
    (h2 : N * Nat.gcd 2 (p ^ (2 * f) - 1) =
      (p ^ (2 * f)) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ (2 * f)) ^ i - 1))
    (hv : 4 * (4 - 1) / 2 * f' = 2 * (2 - 1) / 2 * (2 * f)) : False := by
  obtain ⟨hk3, -⟩ := three_le_and_gcd hp hp2 hf'
  obtain ⟨-, hg⟩ := three_le_and_gcd hp hp2 (by omega : 1 ≤ 2 * f)
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR] at h1
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  rw [hg, Finset.Icc_self, Finset.prod_singleton, pow_two_mul_eq (m := 6) (e := f') (by omega)]
    at hM
  set k := p ^ f'
  have hg1 : 1 ≤ Nat.gcd 4 (k + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hP := (Nat.mul_le_mul_left 4 (prod_unitary_le_prod k 4)).trans
    (four_mul_prod_Icc_pow_add_one_le hk3 (by norm_num : 2 ≤ 4))
  rw [show ∑ i ∈ Finset.Icc 2 4, i = 9 by decide] at hP
  have hle := Nat.le_mul_of_pos_right ((k ^ 6) ^ 2 - 1) hg1
  have h12 : (k ^ 6) ^ 2 = k ^ 3 * k ^ 9 := by ring
  have h27 : 27 * k ^ 9 ≤ k ^ 3 * k ^ 9 :=
    Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_left hk3 3)
  have hX : 1 ≤ k ^ 9 := Nat.one_le_pow _ _ (by omega)
  omega

theorem false_of_card_psp_l2 {p f e m N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (he : 1 ≤ e) (hm : 2 ≤ m)
    (h1 : N * Nat.gcd 2 (p ^ e - 1) =
      (p ^ e) ^ (m ^ 2) * ∏ i ∈ Finset.Icc 1 m, ((p ^ e) ^ (2 * i) - 1))
    (h2 : N * Nat.gcd 2 (p ^ (2 * f) - 1) =
      (p ^ (2 * f)) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ (2 * f)) ^ i - 1))
    (hv : m ^ 2 * e = 2 * (2 - 1) / 2 * (2 * f)) : False := by
  obtain ⟨hk3, hg'⟩ := three_le_and_gcd hp hp2 he
  obtain ⟨-, hg⟩ := three_le_and_gcd hp hp2 (by omega : 1 ≤ 2 * f)
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR, hg'] at h1
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  have hv' : m ^ 2 * e = 2 * f := by simpa using hv
  rw [hg, Finset.Icc_self, Finset.prod_singleton, pow_two_mul_eq hv'] at hM
  set k := p ^ e
  have hM' : ∏ i ∈ Finset.Icc 1 m, (k ^ (2 * i) - 1) = (k ^ (m ^ 2)) ^ 2 - 1 := by omega
  have hP := prod_Icc_pow_two_mul_sub_one_le k m
  rw [hM'] at hP
  have hE : m * (m + 1) + 2 ≤ m ^ 2 * 2 := by nlinarith
  have hbig : 9 * k ^ (m * (m + 1)) ≤ (k ^ (m ^ 2)) ^ 2 := by
    calc 9 * k ^ (m * (m + 1)) ≤ k ^ 2 * k ^ (m * (m + 1)) :=
          Nat.mul_le_mul_right _ (by nlinarith)
      _ = k ^ (m * (m + 1) + 2) := by ring
      _ ≤ k ^ (m ^ 2 * 2) := Nat.pow_le_pow_right (by omega) hE
      _ = (k ^ (m ^ 2)) ^ 2 := by ring
  have hX : 1 ≤ k ^ (m * (m + 1)) := Nat.one_le_pow _ _ (by omega)
  omega

end CFSG.ComponentClassification.CatLeafProof.X10Sp

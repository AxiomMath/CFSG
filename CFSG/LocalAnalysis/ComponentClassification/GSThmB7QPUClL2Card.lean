module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRecog

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeafProof.X10Sp
open CFSG.ComponentClassification.CatLeafProof.X10Lin

theorem false_of_card_psl_l2g {p g e n N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 1 ≤ g)
    (he : 1 ≤ e) (hn : 3 ≤ n)
    (h1 : N * Nat.gcd n (p ^ e - 1) =
      (p ^ e) ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, ((p ^ e) ^ i - 1))
    (h2 : N * Nat.gcd 2 (p ^ g - 1) =
      (p ^ g) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ g) ^ i - 1))
    (hv : n * (n - 1) / 2 * e = 2 * (2 - 1) / 2 * g) : False := by
  obtain ⟨hk3, -⟩ := three_le_and_gcd hp hp2 he
  obtain ⟨-, hgcd⟩ := three_le_and_gcd hp hp2 hg
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR] at h1
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  have hv' : n * (n - 1) / 2 * e = g := by simpa using hv
  have hQ : p ^ g = (p ^ e) ^ (n * (n - 1) / 2) := by rw [← pow_mul, ← hv', mul_comm]
  rw [hgcd, Finset.Icc_self, Finset.prod_singleton, hQ] at hM
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

theorem false_of_card_psu_l2g {p g e n N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 1 ≤ g)
    (he : 1 ≤ e) (hn : 3 ≤ n)
    (h1 : N * Nat.gcd n (p ^ e + 1) = (p ^ e) ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (if Even i then (p ^ e) ^ i - 1 else (p ^ e) ^ i + 1))
    (h2 : N * Nat.gcd 2 (p ^ g - 1) =
      (p ^ g) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ g) ^ i - 1))
    (hv : n * (n - 1) / 2 * e = 2 * (2 - 1) / 2 * g) : False := by
  obtain ⟨hk3, -⟩ := three_le_and_gcd hp hp2 he
  obtain ⟨-, hgcd⟩ := three_le_and_gcd hp hp2 hg
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR] at h1
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  have hv' : n * (n - 1) / 2 * e = g := by simpa using hv
  have hQ : p ^ g = (p ^ e) ^ (n * (n - 1) / 2) := by rw [← pow_mul, ← hv', mul_comm]
  rw [hgcd, Finset.Icc_self, Finset.prod_singleton, hQ] at hM
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

theorem false_of_card_psp_l2g {p g e m N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 1 ≤ g)
    (he : 1 ≤ e) (hm : 2 ≤ m)
    (h1 : N * Nat.gcd 2 (p ^ e - 1) =
      (p ^ e) ^ (m ^ 2) * ∏ i ∈ Finset.Icc 1 m, ((p ^ e) ^ (2 * i) - 1))
    (h2 : N * Nat.gcd 2 (p ^ g - 1) =
      (p ^ g) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ g) ^ i - 1))
    (hv : m ^ 2 * e = 2 * (2 - 1) / 2 * g) : False := by
  obtain ⟨hk3, hg'⟩ := three_le_and_gcd hp hp2 he
  obtain ⟨-, hgcd⟩ := three_le_and_gcd hp hp2 hg
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR, hg'] at h1
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  have hv' : m ^ 2 * e = g := by simpa using hv
  have hQ : p ^ g = (p ^ e) ^ (m ^ 2) := by rw [← pow_mul, ← hv', mul_comm]
  rw [hgcd, Finset.Icc_self, Finset.prod_singleton, hQ] at hM
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

theorem false_of_even_orthogonal_l2_bound {r m M c g : ℕ} (hr : 3 ≤ r) (hm : 4 ≤ m)
    (hc : c ≤ 2) (hg : 1 ≤ g) (hM : M * 2 = ((r ^ (m * (m - 1))) ^ 2 - 1) * g)
    (hMb : M ≤ c * r ^ (m ^ 2)) : False := by
  have hE : m ^ 2 + 2 ≤ 2 * (m * (m - 1)) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega]
    nlinarith
  have hbig : 9 * r ^ (m ^ 2) ≤ (r ^ (m * (m - 1))) ^ 2 := by
    calc 9 * r ^ (m ^ 2) ≤ r ^ 2 * r ^ (m ^ 2) := Nat.mul_le_mul_right _ (by nlinarith)
      _ = r ^ (m ^ 2 + 2) := by ring
      _ ≤ r ^ (2 * (m * (m - 1))) := Nat.pow_le_pow_right (by omega) hE
      _ = (r ^ (m * (m - 1))) ^ 2 := by ring
  have hX : 1 ≤ r ^ (m ^ 2) := Nat.one_le_pow _ _ (by omega)
  have hle : (r ^ (m * (m - 1))) ^ 2 - 1 ≤ ((r ^ (m * (m - 1))) ^ 2 - 1) * g :=
    Nat.le_mul_of_pos_right _ hg
  have hMb' : M * 2 ≤ 4 * r ^ (m ^ 2) := by
    calc M * 2 ≤ c * r ^ (m ^ 2) * 2 := Nat.mul_le_mul_right _ hMb
      _ ≤ 2 * r ^ (m ^ 2) * 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
      _ = 4 * r ^ (m ^ 2) := by ring
  omega

theorem false_of_card_pomegaPlus_l2g {p g e m N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : 1 ≤ g) (he : 1 ≤ e) (hm : 4 ≤ m)
    (h1 : N * Nat.gcd 4 ((p ^ e) ^ m - 1) = (p ^ e) ^ (m * (m - 1)) * ((p ^ e) ^ m - 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), ((p ^ e) ^ (2 * i) - 1))
    (h2 : N * Nat.gcd 2 (p ^ g - 1) =
      (p ^ g) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ g) ^ i - 1))
    (hv : m * (m - 1) * e = 2 * (2 - 1) / 2 * g) : False := by
  obtain ⟨hr3, -⟩ := three_le_and_gcd hp hp2 he
  obtain ⟨-, hgcd⟩ := three_le_and_gcd hp hp2 hg
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR, mul_assoc] at h1
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  have hv' : m * (m - 1) * e = g := by simpa using hv
  have hQ : p ^ g = (p ^ e) ^ (m * (m - 1)) := by rw [← pow_mul, ← hv', mul_comm]
  rw [hgcd, Finset.Icc_self, Finset.prod_singleton, hQ] at hM
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
  exact false_of_even_orthogonal_l2_bound hr3 hm (by norm_num)
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) hM hMb

theorem false_of_card_pomegaMinus_l2g {p g e m N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : 1 ≤ g) (he : 1 ≤ e) (hm : 4 ≤ m)
    (h1 : N * Nat.gcd 4 ((p ^ e) ^ m + 1) = (p ^ e) ^ (m * (m - 1)) * ((p ^ e) ^ m + 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), ((p ^ e) ^ (2 * i) - 1))
    (h2 : N * Nat.gcd 2 (p ^ g - 1) =
      (p ^ g) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ g) ^ i - 1))
    (hv : m * (m - 1) * e = 2 * (2 - 1) / 2 * g) : False := by
  obtain ⟨hr3, -⟩ := three_le_and_gcd hp hp2 he
  obtain ⟨-, hgcd⟩ := three_le_and_gcd hp hp2 hg
  have hR := pow_pow_eq_of_mul_eq (p := p) hv
  rw [hR, mul_assoc] at h1
  have hM := mul_eq_mul_of_card_eq (pow_pos (pow_pos hp.pos _) _) h1 h2
  have hv' : m * (m - 1) * e = g := by simpa using hv
  have hQ : p ^ g = (p ^ e) ^ (m * (m - 1)) := by rw [← pow_mul, ← hv', mul_comm]
  rw [hgcd, Finset.Icc_self, Finset.prod_singleton, hQ] at hM
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
  exact false_of_even_orthogonal_l2_bound hr3 hm le_rfl
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) hM hMb

theorem eq_psl2_of_two_lieModels {Y : Type} [Group Y] {t : StatedLieTag} {m p e f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (ht : IsClassicalTag t)
    (hadm : StatedLieAdmissible t m p e) (h : LieModel Y t m p e)
    (hX : LieModel Y .PSL 2 p f) : t = .PSL ∧ m = 2 ∧ e = f := by
  have he : 1 ≤ e := hadm.2.1
  have hm0 : m ≠ 0 := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have := hadm.2.2.1; omega
    · exact fun h0 => by have : 4 ≤ m := hadm.2.2; omega
    · exact fun h0 => by have : 4 ≤ m := hadm.2.2; omega
  obtain ⟨h1, h1p⟩ := lieOrder_of_lieModel_classical ht hp2 hm0 h
  obtain ⟨h2, h2p⟩ := lieOrder_of_lieModel_classical (Or.inl rfl) hp2 (by norm_num) hX
  have hv := h1p.symm.trans h2p
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · have hm : 2 ≤ m := hadm.2.2.1
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · have hv' : 2 * (2 - 1) / 2 * e = 2 * (2 - 1) / 2 * f := hv
      exact ⟨rfl, rfl, by simpa using hv'⟩
    · exact (false_of_card_psl_l2g hp hp2 hf he hm3 h1 h2 hv).elim
  · exact (false_of_card_psu_l2g hp hp2 hf he hadm.2.2.1 h1 h2 hv).elim
  · exact (false_of_card_psp_l2g hp hp2 hf he hadm.2.2.1 h1 h2 hv).elim
  · exact (false_of_card_psp_l2g hp hp2 hf he (by have := hadm.2.2.1; omega)
      (by rw [(three_le_and_gcd hp hp2 he).2]; exact h1) h2 hv).elim
  · exact (false_of_card_pomegaPlus_l2g hp hp2 hf he hadm.2.2 h1 h2 hv).elim
  · exact (false_of_card_pomegaMinus_l2g hp hp2 hf he hadm.2.2 h1 h2 hv).elim

end CFSG.ComponentClassification.GSThmB.QPUCl

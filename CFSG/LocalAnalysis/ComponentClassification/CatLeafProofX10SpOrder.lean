module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpArith
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Sp

theorem mul_eq_mul_of_card_eq {N D₁ D₂ R M₁ M₂ : ℕ} (hR : 0 < R) (h1 : N * D₁ = R * M₁)
    (h2 : N * D₂ = R * M₂) : M₁ * D₂ = M₂ * D₁ := by
  apply Nat.eq_of_mul_eq_mul_left hR
  calc R * (M₁ * D₂) = (R * M₁) * D₂ := by ring
    _ = N * D₁ * D₂ := by rw [h1]
    _ = N * D₂ * D₁ := by ring
    _ = R * M₂ * D₁ := by rw [h2]
    _ = R * (M₂ * D₁) := by ring

theorem pow_pow_eq_of_mul_eq {p f₁ f₂ e₁ e₂ : ℕ} (h : e₁ * f₁ = e₂ * f₂) :
    (p ^ f₁) ^ e₁ = (p ^ f₂) ^ e₂ := by
  rw [← pow_mul, ← pow_mul, mul_comm f₁, mul_comm f₂, h]

theorem three_le_and_gcd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    3 ≤ p ^ f ∧ Nat.gcd 2 (p ^ f - 1) = 2 := by
  have h3 : 3 ≤ p ^ f :=
    (show 3 ≤ p by have := hp.two_le; omega).trans (Nat.le_self_pow (by omega) p)
  obtain ⟨t, ht⟩ : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  refine ⟨h3, Nat.gcd_eq_left ⟨t, by omega⟩⟩

theorem prod_Icc_one_two (q : ℕ) :
    ∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]

theorem false_of_card_psl_psp4 {p f f' n N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hf' : 1 ≤ f') (hn : 3 ≤ n) (hn4 : n ≠ 4)
    (h1 : N * Nat.gcd n (p ^ f' - 1) =
      (p ^ f') ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, ((p ^ f') ^ i - 1))
    (h2 : N * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1))
    (hv : n * (n - 1) / 2 * f' = 2 ^ 2 * f) : False := by
  obtain ⟨hq3, hg⟩ := three_le_and_gcd hp hp2 hf
  obtain ⟨hq'3, -⟩ := three_le_and_gcd hp hp2 hf'
  set q := p ^ f with hqdef
  set q' := p ^ f' with hq'def
  have hR : q' ^ (n * (n - 1) / 2) = q ^ (2 ^ 2) := pow_pow_eq_of_mul_eq hv
  rw [hR] at h1
  rw [prod_Icc_one_two, hg] at h2
  have hM := mul_eq_mul_of_card_eq (by positivity) h1 h2
  set g := Nat.gcd n (q' - 1)
  have hg1 : 1 ≤ g := Nat.gcd_pos_of_pos_left _ (by omega)
  rcases (show n = 3 ∨ 5 ≤ n by omega) with rfl | h5
  ·
    norm_num at hv hR
    obtain ⟨c, rfl⟩ : ∃ c, f' = 4 * c := ⟨f' / 4, by omega⟩
    have hfc : f = 3 * c := by omega
    rw [hfc] at hqdef
    set s := p ^ c with hsdef
    have hs : 3 ≤ s := (three_le_and_gcd hp hp2 (by omega : 1 ≤ c)).1
    have hq'e : q' = s ^ 4 := by
      rw [hq'def, hsdef, ← pow_mul, mul_comm]
    have hqe : q = s ^ 3 := by
      rw [hqdef, hsdef, ← pow_mul, mul_comm]
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at hM
    rw [hq'e, hqe] at hM
    have hg3 : g ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
    have e8 : 1 ≤ (s ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e12 : 1 ≤ (s ^ 4) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have e6 : 1 ≤ (s ^ 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e12' : 1 ≤ (s ^ 3) ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [e8, e12, e6, e12'] at hM
    have hs' : (3 : ℤ) ≤ s := by exact_mod_cast hs
    have hsq : (s : ℤ) ^ 12 - 1 > 0 := by
      have : (3 : ℤ) ^ 12 ≤ (s : ℤ) ^ 12 := pow_le_pow_left₀ (by norm_num) hs' 12
      linarith
    have hg3' : (g : ℤ) ≤ 3 := by exact_mod_cast hg3
    have hk : 2 * ((s : ℤ) ^ 8 - 1) = (g : ℤ) * ((s : ℤ) ^ 6 - 1) := by
      have h' : (2 * ((s : ℤ) ^ 8 - 1)) * ((s : ℤ) ^ 12 - 1) =
          ((g : ℤ) * ((s : ℤ) ^ 6 - 1)) * ((s : ℤ) ^ 12 - 1) := by
        linear_combination hM
      exact mul_right_cancel₀ hsq.ne' h'
    have h6 : (0 : ℤ) ≤ (s : ℤ) ^ 6 - 1 := by
      have : (1 : ℤ) ≤ (s : ℤ) ^ 6 := one_le_pow₀ (by linarith)
      linarith
    have h8 : 9 * (s : ℤ) ^ 6 ≤ (s : ℤ) ^ 8 := by
      have : (9 : ℤ) ≤ (s : ℤ) ^ 2 := by nlinarith
      calc 9 * (s : ℤ) ^ 6 ≤ (s : ℤ) ^ 2 * (s : ℤ) ^ 6 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = (s : ℤ) ^ 8 := by ring
    nlinarith [mul_le_mul_of_nonneg_right hg3' h6]
  ·
    have hS := two_mul_sum_Icc_two (n := n) (by omega)
    have hT : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
    set S := ∑ i ∈ Finset.Icc 2 n, i
    set T := n * (n - 1) / 2
    have hE : 2 * S + 2 ≤ 3 * T := by
      have key : 2 * (n * (n + 1)) ≤ 3 * (n * (n - 1)) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
        rw [show m + 5 - 1 = m + 4 by omega]
        nlinarith
      omega
    have hP := prod_Icc_pow_sub_one_le q' n
    have hlow := psp4_sq_lower hq3
    set M₂ := (q ^ 2 - 1) * (q ^ 4 - 1)
    have hM₂ : M₂ ≤ 2 * q' ^ S := by
      calc M₂ ≤ M₂ * g := Nat.le_mul_of_pos_right _ hg1
        _ = (∏ i ∈ Finset.Icc 2 n, (q' ^ i - 1)) * 2 := hM.symm
        _ ≤ q' ^ S * 2 := Nat.mul_le_mul_right _ hP
        _ = 2 * q' ^ S := by ring
    have h12 : q ^ 12 = q' ^ (3 * T) := by
      rw [pow_mul', hR]
      ring
    have hq'S : 0 < q' ^ (2 * S) := by positivity
    have hbig : 9 * q' ^ (2 * S) ≤ q' ^ (3 * T) := by
      calc 9 * q' ^ (2 * S) ≤ q' ^ 2 * q' ^ (2 * S) :=
            Nat.mul_le_mul_right _ (by nlinarith)
        _ = q' ^ (2 * S + 2) := by ring
        _ ≤ q' ^ (3 * T) := Nat.pow_le_pow_right (by omega) hE
    have hsq : M₂ ^ 2 ≤ 4 * q' ^ (2 * S) := by
      calc M₂ ^ 2 ≤ (2 * q' ^ S) ^ 2 := Nat.pow_le_pow_left hM₂ 2
        _ = 4 * q' ^ (2 * S) := by ring
    rw [h12] at hlow
    omega

theorem prod_unitary_le_prod (q n : ℕ) :
    ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1) ≤
      ∏ i ∈ Finset.Icc 2 n, (q ^ i + 1) :=
  Finset.prod_le_prod fun i _ => by
    split_ifs
    · omega
    · exact le_rfl

theorem false_of_psu3_eq {s g : ℤ} (hs : 3 ≤ s) (hg : g ≤ 3)
    (h : (s ^ 8 - 1) * (s ^ 12 + 1) * 2 = (s ^ 6 - 1) * (s ^ 12 - 1) * g) : False := by
  have h6 : 0 ≤ s ^ 6 - 1 := by
    have : 1 ≤ s ^ 6 := one_le_pow₀ (by linarith)
    linarith
  have h12 : 0 < s ^ 12 - 1 := by
    have : (3 : ℤ) ^ 12 ≤ s ^ 12 := pow_le_pow_left₀ (by norm_num) hs 12
    linarith
  have h8 : 9 * s ^ 6 ≤ s ^ 8 := by
    have : (9 : ℤ) ≤ s ^ 2 := by nlinarith
    calc 9 * s ^ 6 ≤ s ^ 2 * s ^ 6 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = s ^ 8 := by ring
  have hlt : 3 * (s ^ 6 - 1) < 2 * (s ^ 8 - 1) := by linarith
  have hA : 3 * (s ^ 6 - 1) * (s ^ 12 - 1) < 2 * (s ^ 8 - 1) * (s ^ 12 - 1) :=
    mul_lt_mul_of_pos_right hlt h12
  have hB : (s ^ 6 - 1) * (s ^ 12 - 1) * g ≤ (s ^ 6 - 1) * (s ^ 12 - 1) * 3 :=
    mul_le_mul_of_nonneg_left hg (mul_nonneg h6 h12.le)
  have hC : 2 * (s ^ 8 - 1) * (s ^ 12 - 1) + 4 * (s ^ 8 - 1) =
      (s ^ 8 - 1) * (s ^ 12 + 1) * 2 := by ring
  linarith

theorem false_of_card_psu_psp4 {p f f' n N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hf' : 1 ≤ f') (hn : 3 ≤ n) (hn4 : n ≠ 4)
    (h1 : N * Nat.gcd n (p ^ f' + 1) = (p ^ f') ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (if Even i then (p ^ f') ^ i - 1 else (p ^ f') ^ i + 1))
    (h2 : N * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1))
    (hv : n * (n - 1) / 2 * f' = 2 ^ 2 * f) : False := by
  obtain ⟨hq3, hg⟩ := three_le_and_gcd hp hp2 hf
  obtain ⟨hq'3, -⟩ := three_le_and_gcd hp hp2 hf'
  set q := p ^ f with hqdef
  set q' := p ^ f' with hq'def
  have hR : q' ^ (n * (n - 1) / 2) = q ^ (2 ^ 2) := pow_pow_eq_of_mul_eq hv
  rw [hR] at h1
  rw [prod_Icc_one_two, hg] at h2
  have hM := mul_eq_mul_of_card_eq (by positivity) h1 h2
  set g := Nat.gcd n (q' + 1)
  have hg1 : 1 ≤ g := Nat.gcd_pos_of_pos_left _ (by omega)
  rcases (show n = 3 ∨ 5 ≤ n by omega) with rfl | h5
  ·
    norm_num at hv hR
    obtain ⟨c, rfl⟩ : ∃ c, f' = 4 * c := ⟨f' / 4, by omega⟩
    have hfc : f = 3 * c := by omega
    rw [hfc] at hqdef
    set s := p ^ c with hsdef
    have hs : 3 ≤ s := (three_le_and_gcd hp hp2 (by omega : 1 ≤ c)).1
    have hq'e : q' = s ^ 4 := by
      rw [hq'def, hsdef, ← pow_mul, mul_comm]
    have hqe : q = s ^ 3 := by
      rw [hqdef, hsdef, ← pow_mul, mul_comm]
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at hM
    simp only [show Even 2 by decide, show ¬ Even 3 by decide, ↓reduceIte] at hM
    rw [hq'e, hqe] at hM
    have hg3 : g ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
    have e8 : 1 ≤ (s ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e6 : 1 ≤ (s ^ 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e12' : 1 ≤ (s ^ 3) ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [e8, e6, e12'] at hM
    exact false_of_psu3_eq (s := (s : ℤ)) (g := (g : ℤ)) (by exact_mod_cast hs)
      (by exact_mod_cast hg3) (by linear_combination hM)
  ·
    have hS := two_mul_sum_Icc_two (n := n) (by omega)
    have hT : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
    set S := ∑ i ∈ Finset.Icc 2 n, i
    set T := n * (n - 1) / 2
    have hE : 2 * S + 2 ≤ 3 * T := by
      have key : 2 * (n * (n + 1)) ≤ 3 * (n * (n - 1)) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
        rw [show m + 5 - 1 = m + 4 by omega]
        nlinarith
      omega
    have hP4 : 4 * ∏ i ∈ Finset.Icc 2 n, (if Even i then q' ^ i - 1 else q' ^ i + 1) ≤
        5 * q' ^ S :=
      (Nat.mul_le_mul_left 4 (prod_unitary_le_prod q' n)).trans
        (four_mul_prod_Icc_pow_add_one_le hq'3 (by omega))
    have hlow := psp4_sq_lower hq3
    set M₂ := (q ^ 2 - 1) * (q ^ 4 - 1)
    have hM₂ : 2 * M₂ ≤ 5 * q' ^ S := by
      calc 2 * M₂ ≤ 2 * (M₂ * g) := Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ hg1)
        _ = 4 * ∏ i ∈ Finset.Icc 2 n, (if Even i then q' ^ i - 1 else q' ^ i + 1) := by
          rw [← hM]
          ring
        _ ≤ 5 * q' ^ S := hP4
    have h12 : q ^ 12 = q' ^ (3 * T) := by
      rw [pow_mul', hR]
      ring
    have hbig : 9 * q' ^ (2 * S) ≤ q' ^ (3 * T) := by
      calc 9 * q' ^ (2 * S) ≤ q' ^ 2 * q' ^ (2 * S) :=
            Nat.mul_le_mul_right _ (by nlinarith)
        _ = q' ^ (2 * S + 2) := by ring
        _ ≤ q' ^ (3 * T) := Nat.pow_le_pow_right (by omega) hE
    have hsq : 4 * M₂ ^ 2 ≤ 25 * q' ^ (2 * S) := by
      calc 4 * M₂ ^ 2 = (2 * M₂) ^ 2 := by ring
        _ ≤ (5 * q' ^ S) ^ 2 := Nat.pow_le_pow_left hM₂ 2
        _ = 25 * q' ^ (2 * S) := by ring
    have hq'S : 0 < q' ^ (2 * S) := by positivity
    rw [h12] at hlow
    omega

theorem false_of_card_psp_psp4 {p f f' m N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hf' : 1 ≤ f') (hm : 3 ≤ m)
    (h1 : N * Nat.gcd 2 (p ^ f' - 1) =
      (p ^ f') ^ (m ^ 2) * ∏ i ∈ Finset.Icc 1 m, ((p ^ f') ^ (2 * i) - 1))
    (h2 : N * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1))
    (hv : m ^ 2 * f' = 2 ^ 2 * f) : False := by
  obtain ⟨hq3, hg⟩ := three_le_and_gcd hp hp2 hf
  obtain ⟨hr3, hg'⟩ := three_le_and_gcd hp hp2 hf'
  set q := p ^ f
  set r := p ^ f'
  have hR : r ^ (m ^ 2) = q ^ (2 ^ 2) := pow_pow_eq_of_mul_eq hv
  rw [hR, hg'] at h1
  rw [prod_Icc_one_two, hg] at h2
  have hM := mul_eq_mul_of_card_eq (by positivity) h1 h2
  have hM' : ∏ i ∈ Finset.Icc 1 m, (r ^ (2 * i) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by omega
  have hP := prod_Icc_pow_two_mul_sub_one_le r m
  rw [hM'] at hP
  have hlow := psp4_sq_lower hq3
  have h12 : q ^ 12 = r ^ (3 * m ^ 2) := by
    rw [pow_mul', hR]
    ring
  have hE : m * (m + 1) * 2 + 3 ≤ 3 * m ^ 2 := by nlinarith
  have hbig : 27 * r ^ (m * (m + 1) * 2) ≤ r ^ (3 * m ^ 2) := by
    calc 27 * r ^ (m * (m + 1) * 2) ≤ r ^ 3 * r ^ (m * (m + 1) * 2) :=
          Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_left hr3 3)
      _ = r ^ (m * (m + 1) * 2 + 3) := by ring
      _ ≤ r ^ (3 * m ^ 2) := Nat.pow_le_pow_right (by omega) hE
  have hsq : ((q ^ 2 - 1) * (q ^ 4 - 1)) ^ 2 ≤ r ^ (m * (m + 1) * 2) := by
    calc ((q ^ 2 - 1) * (q ^ 4 - 1)) ^ 2 ≤ (r ^ (m * (m + 1))) ^ 2 := Nat.pow_le_pow_left hP 2
      _ = r ^ (m * (m + 1) * 2) := by ring
  have hpos : 0 < r ^ (m * (m + 1) * 2) := by positivity
  rw [h12] at hlow
  omega

end CFSG.ComponentClassification.CatLeafProof.X10Sp

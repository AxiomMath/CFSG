module

public import CFSG.LocalAnalysis.SeitzReduction.CrossCharEven
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharOdd

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof CFSG.SeitzReduction.CrossChar
open CFSG.SeitzReduction.RankOne.LieOdd

namespace L4Order

def cofL4 (Q : ℕ) : ℕ := (Q ^ 2 - 1) * (Q ^ 3 - 1) * (Q ^ 4 - 1)

theorem nine_lt {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 9 < 2 * cofL4 Q := by
  have h2 : 4 ≤ Q ^ 2 := by nlinarith
  have h3 : 8 ≤ Q ^ 3 := by nlinarith [Nat.pow_le_pow_left hQ 3]
  have h4 : 16 ≤ Q ^ 4 := by nlinarith [Nat.pow_le_pow_left hQ 4]
  have e1 : 3 * Q ^ 2 ≤ 4 * (Q ^ 2 - 1) := by omega
  have e2 : 7 * Q ^ 3 ≤ 8 * (Q ^ 3 - 1) := by omega
  have e3 : 15 * Q ^ 4 ≤ 16 * (Q ^ 4 - 1) := by omega
  have h := Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3
  have hQ9 : 0 < Q ^ 9 := by positivity
  have h5 : (3 * Q ^ 2) * (7 * Q ^ 3) * (15 * Q ^ 4) = 315 * Q ^ 9 := by ring
  have h6 : (4 * (Q ^ 2 - 1)) * (8 * (Q ^ 3 - 1)) * (16 * (Q ^ 4 - 1)) =
      512 * ((Q ^ 2 - 1) * (Q ^ 3 - 1) * (Q ^ 4 - 1)) := by ring
  unfold cofL4
  omega

theorem cofL4_lt {Q : ℕ} (hQ : 1 ≤ Q) : cofL4 Q < Q ^ 9 := by
  have h2 := pow_sub_one_lt_pow hQ 2
  have h3 := pow_sub_one_lt_pow hQ 3
  have h4 := pow_sub_one_lt_pow hQ 4
  calc cofL4 Q = (Q ^ 2 - 1) * (Q ^ 3 - 1) * (Q ^ 4 - 1) := rfl
    _ < Q ^ 2 * Q ^ 3 * Q ^ 4 := Nat.mul_lt_mul'' (Nat.mul_lt_mul'' h2 h3) h4
    _ = Q ^ 9 := by ring

theorem two_le_two_pow {f : ℕ} (hf : 1 ≤ f) : 2 ≤ 2 ^ f :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem even_two_pow {f : ℕ} (hf : 1 ≤ f) : Even (2 ^ f) :=
  Nat.even_pow.mpr ⟨even_two, by omega⟩

theorem odd_cofL4 {Q : ℕ} (hQ : Even Q) (hQ2 : 2 ≤ Q) : Odd (cofL4 Q) := by
  have h : ∀ k, 1 ≤ k → Odd (Q ^ k - 1) := fun k hk =>
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (hQ.pow_of_ne_zero (by omega)) odd_one
  exact ((h 2 (by norm_num)).mul (h 3 (by norm_num))).mul (h 4 (by norm_num))

theorem gcd_two_pow_eq_one {k x : ℕ} (hx : Odd x) : Nat.gcd (2 ^ k) x = 1 :=
  Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx)

theorem lieOrderNumerator_psl_four (Q : ℕ) :
    lieOrderNumerator .PSL 4 Q = Q ^ 6 * cofL4 Q := by
  simp [lieOrderNumerator, cofL4, Finset.prod_Icc_succ_top]

theorem lieOrderDivisor_psl_four {g : ℕ} (hg : 1 ≤ g) : lieOrderDivisor .PSL 4 (2 ^ g) = 1 := by
  show Nat.gcd 4 (2 ^ g - 1) = 1
  have hodd : Odd (2 ^ g - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) (even_two_pow hg) odd_one
  simpa using gcd_two_pow_eq_one (k := 2) hodd

theorem lieOrderDivisor_psp_two {f : ℕ} (hf : 1 ≤ f) : lieOrderDivisor .PSp 2 (2 ^ f) = 1 := by
  show Nat.gcd 2 (2 ^ f - 1) = 1
  have hodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) (even_two_pow hf) odd_one
  simpa using gcd_two_pow_eq_one (k := 1) hodd

theorem lieOrderDivisor_psu_four {f : ℕ} (hf : 1 ≤ f) : lieOrderDivisor .PSU 4 (2 ^ f) = 1 := by
  show Nat.gcd 4 (2 ^ f + 1) = 1
  simpa using gcd_two_pow_eq_one (k := 2) (even_two_pow hf).add_one

theorem cof_psl_two (q : ℕ) : lieOrderCofactor .PSL 2 q = q ^ 2 - 1 := by
  simp [lieOrderCofactor]

theorem cof_psl_three (q : ℕ) : lieOrderCofactor .PSL 3 q = (q ^ 2 - 1) * (q ^ 3 - 1) := by
  simp [lieOrderCofactor, Finset.prod_Icc_succ_top]

theorem cof_psu_three (q : ℕ) : lieOrderCofactor .PSU 3 q = (q ^ 2 - 1) * (q ^ 3 + 1) := by
  simp [lieOrderCofactor, Finset.prod_Icc_succ_top, Nat.even_iff]

theorem cof_psu_four (q : ℕ) :
    lieOrderCofactor .PSU 4 q = (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) := by
  simp [lieOrderCofactor, Finset.prod_Icc_succ_top, Nat.even_iff]

theorem cof_psp_two (q : ℕ) : lieOrderCofactor .PSp 2 q = (q ^ 2 - 1) * (q ^ 4 - 1) := by
  simp [lieOrderCofactor, Finset.prod_Icc_succ_top]

theorem sylow_and_cofactor {t : StatedLieTag} {n f g M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hg : 1 ≤ g) (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hM' : M = (2 ^ g) ^ 6 * cofL4 (2 ^ g)) :
    lieSylowExponent t n * f = 6 * g ∧
      cofL4 (2 ^ g) * lieOrderDivisor t n (2 ^ f) = lieOrderCofactor t n (2 ^ f) := by
  have hodd : Odd (cofL4 (2 ^ g)) := odd_cofL4 (even_two_pow hg) (two_le_two_pow hg)
  have hT := ordProj_two_eq_of_two hadm hM
  have hpow : (2 ^ g) ^ 6 = 2 ^ (6 * g) := by rw [← pow_mul, mul_comm]
  rw [hM', hpow, ordProj_two_pow_mul_odd hodd] at hT
  have hNf : lieSylowExponent t n * f = 6 * g := (Nat.pow_right_injective le_rfl hT).symm
  refine ⟨hNf, ?_⟩
  rw [lieOrderNumerator_eq hadm, ← pow_mul, mul_comm f, hNf, hM', hpow] at hM
  have hpos : 0 < 2 ^ (6 * g) := by positivity
  have h : 2 ^ (6 * g) * (cofL4 (2 ^ g) * lieOrderDivisor t n (2 ^ f)) =
      2 ^ (6 * g) * lieOrderCofactor t n (2 ^ f) := by
    rw [← hM]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos h

theorem false_of_size {q Q m C D E N : ℕ} (hq : 2 ≤ q) (hqN : q ^ N = Q ^ 6)
    (hE : 2 * E + 2 ≤ 3 * N) (hC : C ≤ q ^ E) (hmC : m * D = C) (hD : 1 ≤ D)
    (hm : Q ^ 9 < 2 * m) : False := by
  have h1 : m ≤ q ^ E := by
    calc m = m * 1 := (mul_one m).symm
      _ ≤ m * D := Nat.mul_le_mul_left _ hD
      _ = C := hmC
      _ ≤ q ^ E := hC
  have h2 : (Q ^ 9) ^ 2 < (2 * m) ^ 2 := Nat.pow_lt_pow_left hm (by norm_num)
  have h3 : (2 * m) ^ 2 ≤ 4 * (q ^ E) ^ 2 := by
    calc (2 * m) ^ 2 = 4 * m ^ 2 := by ring
      _ ≤ 4 * (q ^ E) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
  have h4 : 4 * (q ^ E) ^ 2 ≤ q ^ (3 * N) := by
    calc 4 * (q ^ E) ^ 2 ≤ q ^ 2 * (q ^ E) ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
      _ = q ^ (2 * E + 2) := by ring
      _ ≤ q ^ (3 * N) := Nat.pow_le_pow_right (by omega) hE
  have h5 : q ^ (3 * N) = (Q ^ 9) ^ 2 := by
    rw [pow_mul', hqN]; ring
  omega

theorem psl_two_false {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ 2)
    (h : cofL4 Q * D = (Q ^ 6) ^ 2 - 1) : False := by
  have h1 : cofL4 Q < Q ^ 9 := cofL4_lt (by omega)
  have h3 : 8 ≤ Q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
  have h4 : 0 < Q ^ 9 := by positivity
  have h2 : 2 * Q ^ 9 + 1 ≤ (Q ^ 6) ^ 2 := by
    have : (Q ^ 6) ^ 2 = Q ^ 9 * Q ^ 3 := by ring
    nlinarith
  have h5 : cofL4 Q * D ≤ cofL4 Q * 2 := Nat.mul_le_mul_left _ hD
  omega

theorem psl_three_false {Q D : ℕ} (hQ : 4 ≤ Q) (hD : D ≤ 3)
    (h : cofL4 Q * D = ((Q ^ 2) ^ 2 - 1) * ((Q ^ 2) ^ 3 - 1)) : False := by
  have e1 : (Q ^ 2) ^ 2 = Q ^ 4 := by ring
  have e2 : (Q ^ 2) ^ 3 = Q ^ 6 := by ring
  rw [e1, e2] at h
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold cofL4 at h
  zify [h2, h3, h4, h6] at h
  have hx : (4 : ℤ) ≤ Q := by exact_mod_cast hQ
  have hDz : (D : ℤ) ≤ 3 := by exact_mod_cast hD
  have hD0 : (0 : ℤ) ≤ D := by positivity
  generalize (Q : ℤ) = x at *
  have hx2 : (16 : ℤ) ≤ x ^ 2 := by nlinarith
  have hx3 : (64 : ℤ) ≤ x ^ 3 := by nlinarith
  have hx4 : (256 : ℤ) ≤ x ^ 4 := by nlinarith
  have key : (x ^ 4 - 1) * (x ^ 3 - 1) * ((x ^ 2 - 1) * D - (x ^ 3 + 1)) = 0 := by
    linear_combination h
  have hne : (x ^ 4 - 1) * (x ^ 3 - 1) ≠ 0 :=
    mul_ne_zero (by linarith : (0 : ℤ) < x ^ 4 - 1).ne' (by linarith : (0 : ℤ) < x ^ 3 - 1).ne'
  have key2 : (x ^ 2 - 1) * D = x ^ 3 + 1 := by
    have := (mul_eq_zero.mp key).resolve_left hne
    linarith
  have h7 : (x ^ 2 - 1) * D ≤ (x ^ 2 - 1) * 3 :=
    mul_le_mul_of_nonneg_left hDz (by linarith)
  have h8 : 4 * x ^ 2 ≤ x ^ 3 := by nlinarith
  linarith

theorem psu_three_false {Q D : ℕ} (hQ : 4 ≤ Q) (hD : D ≤ 3)
    (h : cofL4 Q * D = ((Q ^ 2) ^ 2 - 1) * ((Q ^ 2) ^ 3 + 1)) : False := by
  have e1 : (Q ^ 2) ^ 2 = Q ^ 4 := by ring
  have e2 : (Q ^ 2) ^ 3 = Q ^ 6 := by ring
  rw [e1, e2] at h
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold cofL4 at h
  zify [h2, h3, h4] at h
  have hx : (4 : ℤ) ≤ Q := by exact_mod_cast hQ
  have hDz : (D : ℤ) ≤ 3 := by exact_mod_cast hD
  have hD0 : (0 : ℤ) ≤ D := by positivity
  generalize (Q : ℤ) = x at *
  have hx2 : (16 : ℤ) ≤ x ^ 2 := by nlinarith
  have hx3 : (64 : ℤ) ≤ x ^ 3 := by nlinarith
  have hx4 : (256 : ℤ) ≤ x ^ 4 := by nlinarith
  have key : (x ^ 4 - 1) * ((x ^ 2 - 1) * (x ^ 3 - 1) * D - (x ^ 6 + 1)) = 0 := by
    linear_combination h
  have key2 : (x ^ 2 - 1) * (x ^ 3 - 1) * D = x ^ 6 + 1 := by
    have := (mul_eq_zero.mp key).resolve_left (by linarith : (0 : ℤ) < x ^ 4 - 1).ne'
    linarith
  have h7 : (x ^ 2 - 1) * (x ^ 3 - 1) * D ≤ (x ^ 2 - 1) * (x ^ 3 - 1) * 3 :=
    mul_le_mul_of_nonneg_left hDz (mul_nonneg (by linarith) (by linarith))
  have h8 : 4 * x ^ 5 ≤ x ^ 6 := by nlinarith [pow_nonneg (by linarith : (0 : ℤ) ≤ x) 5]
  have h9 : 0 ≤ x ^ 5 := by positivity
  nlinarith

theorem psu_four_false {Q : ℕ} (hQ : 2 ≤ Q)
    (h : cofL4 Q * 1 = (Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1)) : False := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold cofL4 at h
  zify [h2, h3, h4] at h
  have hx : (2 : ℤ) ≤ Q := by exact_mod_cast hQ
  generalize (Q : ℤ) = x at *
  have hx2 : (4 : ℤ) ≤ x ^ 2 := by nlinarith
  have hx4 : (16 : ℤ) ≤ x ^ 4 := by nlinarith
  have key : (x ^ 2 - 1) * (x ^ 4 - 1) * (-2) = 0 := by linear_combination h
  have hpos : 0 < (x ^ 2 - 1) * (x ^ 4 - 1) :=
    mul_pos (by linarith) (by linarith)
  linarith

theorem psp_two_false {q Q : ℕ} (hq : q ^ 2 = Q ^ 3) (hQ : 2 ≤ Q)
    (h : cofL4 Q * 1 = (q ^ 2 - 1) * (q ^ 4 - 1)) : False := by
  have e4 : q ^ 4 = Q ^ 6 := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq]; ring
  rw [e4, hq] at h
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold cofL4 at h
  zify [h2, h3, h4, h6] at h
  have hx : (2 : ℤ) ≤ Q := by exact_mod_cast hQ
  generalize (Q : ℤ) = x at *
  have hx2 : (4 : ℤ) ≤ x ^ 2 := by nlinarith
  have hx3 : (8 : ℤ) ≤ x ^ 3 := by nlinarith
  have hx4 : (16 : ℤ) ≤ x ^ 4 := by nlinarith
  have key : (x ^ 3 - 1) * ((x ^ 2 - 1) * (x ^ 4 - 1) - (x ^ 6 - 1)) = 0 := by
    linear_combination h
  have key2 := (mul_eq_zero.mp key).resolve_left (by linarith : (0 : ℤ) < x ^ 3 - 1).ne'
  have e6 : x ^ 6 = x ^ 2 * x ^ 4 := by ring
  nlinarith

theorem b2_false {q Q : ℕ} (hq : q = Q ^ 3) (hQ : 2 ≤ Q)
    (h : cofL4 Q * 1 = (q ^ 2 + 1) * (q - 1)) : False := by
  subst hq
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold cofL4 at h
  zify [h2, h3, h4] at h
  have hx : (2 : ℤ) ≤ Q := by exact_mod_cast hQ
  generalize (Q : ℤ) = x at *
  have hx2 : (4 : ℤ) ≤ x ^ 2 := by nlinarith
  have hx3 : (8 : ℤ) ≤ x ^ 3 := by nlinarith
  have hx4 : (16 : ℤ) ≤ x ^ 4 := by nlinarith
  have key : (x ^ 3 - 1) * ((x ^ 2 - 1) * (x ^ 4 - 1) - (x ^ 6 + 1)) = 0 := by
    linear_combination h
  have key2 := (mul_eq_zero.mp key).resolve_left (by linarith : (0 : ℤ) < x ^ 3 - 1).ne'
  have e6 : x ^ 6 = x ^ 2 * x ^ 4 := by ring
  nlinarith

theorem core {t : StatedLieTag} {n f g : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hg : 2 ≤ g)
    (hNf : lieSylowExponent t n * f = 6 * g)
    (hmC : cofL4 (2 ^ g) * lieOrderDivisor t n (2 ^ f) = lieOrderCofactor t n (2 ^ f)) :
    t = .PSL ∧ n = 4 ∧ f = g := by
  have hf : 1 ≤ f := hadm.2.1
  have hq : 2 ≤ 2 ^ f := two_le_two_pow hf
  have hq1 : 1 ≤ 2 ^ f := by omega
  have hQ : 2 ≤ 2 ^ g := two_le_two_pow (by omega)
  have hQ4 : 4 ≤ 2 ^ g :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hD : 1 ≤ lieOrderDivisor t n (2 ^ f) :=
    Nat.one_le_iff_ne_zero.mpr (lieOrderDivisor_ne_zero hadm)
  have hqN : (2 ^ f) ^ lieSylowExponent t n = (2 ^ g) ^ 6 := by
    rw [← pow_mul, ← pow_mul, mul_comm f, hNf, mul_comm]
  have hm : (2 ^ g) ^ 9 < 2 * cofL4 (2 ^ g) := nine_lt hQ
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    rcases (by omega : n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with rfl | rfl | rfl | h5
    · exfalso
      have hf6 : f = 6 * g := by simp [lieSylowExponent] at hNf; omega
      have hqQ : 2 ^ f = (2 ^ g) ^ 6 := by rw [← pow_mul, mul_comm, hf6]
      have hD2 : lieOrderDivisor .PSL 2 (2 ^ f) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
      generalize lieOrderDivisor .PSL 2 (2 ^ f) = D at hmC hD2
      rw [cof_psl_two, hqQ] at hmC
      exact psl_two_false hQ hD2 hmC
    · exfalso
      have hf2 : f = 2 * g := by simp [lieSylowExponent] at hNf; omega
      have hqQ : 2 ^ f = (2 ^ g) ^ 2 := by rw [← pow_mul, mul_comm, hf2]
      have hD3 : lieOrderDivisor .PSL 3 (2 ^ f) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
      generalize lieOrderDivisor .PSL 3 (2 ^ f) = D at hmC hD3
      rw [cof_psl_three, hqQ] at hmC
      exact psl_three_false hQ4 hD3 hmC
    · exact ⟨rfl, rfl, by simp [lieSylowExponent] at hNf; omega⟩
    · exfalso
      have hC : lieOrderCofactor .PSL n (2 ^ f) ≤ (2 ^ f) ^ (n * (n - 1) / 2 + n - 1) :=
        (prod_Icc_two_sub_one_lt hq1 hn).le
      refine false_of_size hq hqN ?_ hC hmC hD hm
      show 2 * (n * (n - 1) / 2 + n - 1) + 2 ≤ 3 * (n * (n - 1) / 2)
      have h2N := two_mul_tri n
      have h4 : n * 4 ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
      omega
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    rcases (by omega : n = 3 ∨ n = 4 ∨ 5 ≤ n) with rfl | rfl | h5
    · exfalso
      have hf2 : f = 2 * g := by simp [lieSylowExponent] at hNf; omega
      have hqQ : 2 ^ f = (2 ^ g) ^ 2 := by rw [← pow_mul, mul_comm, hf2]
      have hD3 : lieOrderDivisor .PSU 3 (2 ^ f) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
      generalize lieOrderDivisor .PSU 3 (2 ^ f) = D at hmC hD3
      rw [cof_psu_three, hqQ] at hmC
      exact psu_three_false hQ4 hD3 hmC
    · exfalso
      have hfg : f = g := by simp [lieSylowExponent] at hNf; omega
      rw [lieOrderDivisor_psu_four hf, cof_psu_four, hfg] at hmC
      exact psu_four_false hQ hmC
    · exfalso
      have hC : lieOrderCofactor .PSU n (2 ^ f) ≤ (2 ^ f) ^ (n * (n - 1) / 2 + n - 1) :=
        (prod_psu_lt hq (by omega)).le
      refine false_of_size hq hqN ?_ hC hmC hD hm
      show 2 * (n * (n - 1) / 2 + n - 1) + 2 ≤ 3 * (n * (n - 1) / 2)
      have h2N := two_mul_tri n
      have h4 : n * 4 ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
      omega
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | h3
    · exfalso
      have h2f : 2 * f = 3 * g := by simp [lieSylowExponent] at hNf; omega
      have hq2 : (2 ^ f) ^ 2 = (2 ^ g) ^ 3 := by
        rw [← pow_mul, ← pow_mul]; congr 1; omega
      rw [lieOrderDivisor_psp_two hf, cof_psp_two] at hmC
      exact psp_two_false hq2 hQ hmC
    · exfalso
      have hC : lieOrderCofactor .PSp n (2 ^ f) ≤ (2 ^ f) ^ (n * (n + 1)) :=
        (prod_Icc_one_sub_one_lt hq1 (by omega)).le
      refine false_of_size hq hqN ?_ hC hmC hD hm
      show 2 * (n * (n + 1)) + 2 ≤ 3 * n ^ 2
      nlinarith
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    exfalso
    have hP := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n - 1)
    have hC : lieOrderCofactor .POmegaPlus n (2 ^ f) ≤
        (2 ^ f) ^ (n + (n - 1) * (n - 1 + 1)) := by
      rw [pow_add]
      exact (Nat.mul_lt_mul'' (pow_sub_one_lt_pow hq1 n) hP).le
    refine false_of_size hq hqN ?_ hC hmC hD hm
    show 2 * (n + (n - 1) * (n - 1 + 1)) + 2 ≤ 3 * (n * (n - 1))
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simp only [show k + 4 - 1 = k + 3 by omega]
    nlinarith
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    exfalso
    have hP := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n - 1)
    have hX : (2 ^ f) ^ n + 1 ≤ (2 ^ f) ^ (n + 1) := pow_add_one_le_pow_succ hq n
    have hC : lieOrderCofactor .POmegaMinus n (2 ^ f) ≤
        (2 ^ f) ^ (n + 1 + (n - 1) * (n - 1 + 1)) := by
      rw [pow_add]
      exact (Nat.mul_lt_mul_of_le_of_lt hX hP (by positivity)).le
    refine false_of_size hq hqN ?_ hC hmC hD hm
    show 2 * (n + 1 + (n - 1) * (n - 1 + 1)) + 2 ≤ 3 * (n * (n - 1))
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simp only [show k + 4 - 1 = k + 3 by omega]
    nlinarith
  case G2 =>
    exfalso
    have hC : lieOrderCofactor .G2 n (2 ^ f) ≤ (2 ^ f) ^ 8 := by
      generalize 2 ^ f = q
      show (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 8
      calc (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 8 := by ring
    exact false_of_size hq hqN (by simp [lieSylowExponent]) hC hmC hD hm
  case F4 =>
    exfalso
    have hC : lieOrderCofactor .F4 n (2 ^ f) ≤ (2 ^ f) ^ 28 := by
      generalize 2 ^ f = q
      show (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 28
      calc (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
          ≤ q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 28 := by ring
    exact false_of_size hq hqN (by simp [lieSylowExponent]) hC hmC hD hm
  case E6 =>
    exfalso
    have hC : lieOrderCofactor .E6 n (2 ^ f) ≤ (2 ^ f) ^ 42 := by
      generalize 2 ^ f = q
      show (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) ≤
        q ^ 42
      calc (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)
          ≤ q ^ 12 * q ^ 9 * q ^ 8 * q ^ 6 * q ^ 5 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 42 := by ring
    exact false_of_size hq hqN (by simp [lieSylowExponent]) hC hmC hD hm
  case E7 =>
    exfalso
    have hC : lieOrderCofactor .E7 n (2 ^ f) ≤ (2 ^ f) ^ 70 := by
      generalize 2 ^ f = q
      show (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 70
      calc (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
            (q ^ 6 - 1) * (q ^ 2 - 1)
          ≤ q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 70 := by ring
    exact false_of_size hq hqN (by simp [lieSylowExponent]) hC hmC hD hm
  case E8 =>
    exfalso
    have hC : lieOrderCofactor .E8 n (2 ^ f) ≤ (2 ^ f) ^ 128 := by
      generalize 2 ^ f = q
      show (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
        (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1) ≤ q ^ 128
      calc (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
            (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)
          ≤ q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 8 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 128 := by ring
    exact false_of_size hq hqN (by simp [lieSylowExponent]) hC hmC hD hm
  case twistedE6 =>
    exfalso
    have hC : lieOrderCofactor .twistedE6 n (2 ^ f) ≤ (2 ^ f) ^ 44 := by
      generalize 2 ^ f = q at hq ⊢
      show (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) ≤
        q ^ 44
      calc (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
          ≤ q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 6 * q ^ 2 := by
            gcongr
            · exact Nat.sub_le _ _
            · exact pow_add_one_le_pow_succ hq 9
            · exact Nat.sub_le _ _
            · exact Nat.sub_le _ _
            · exact pow_add_one_le_pow_succ hq 5
            · exact Nat.sub_le _ _
        _ = q ^ 44 := by ring
    exact false_of_size hq hqN (by simp [lieSylowExponent]) hC hmC hD hm
  case trialityD4 =>
    exfalso
    have hC : lieOrderCofactor .trialityD4 n (2 ^ f) ≤ (2 ^ f) ^ 17 := by
      generalize 2 ^ f = q at hq ⊢
      show (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 17
      have h8 : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
        have h4 : q ^ 4 + 1 ≤ q ^ 8 := by
          have : q ^ 4 + 1 ≤ q ^ 5 := pow_add_one_le_pow_succ hq 4
          exact this.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
        have : q ^ 8 + 1 ≤ q ^ 9 := pow_add_one_le_pow_succ hq 8
        nlinarith [Nat.one_le_pow 8 q (by omega)]
      calc (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 9 * q ^ 6 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 17 := by ring
    exact false_of_size hq hqN (by simp [lieSylowExponent]) hC hmC hD hm
  case twistedB2 =>
    exfalso
    have hf3 : f = 3 * g := by simp [lieSylowExponent] at hNf; omega
    have hqQ : 2 ^ f = (2 ^ g) ^ 3 := by rw [← pow_mul, mul_comm, hf3]
    have hD1 : lieOrderDivisor .twistedB2 n (2 ^ f) = 1 := rfl
    have hC : lieOrderCofactor .twistedB2 n (2 ^ f) = ((2 ^ f) ^ 2 + 1) * (2 ^ f - 1) := rfl
    rw [hD1, hC] at hmC
    exact b2_false hqQ hQ hmC
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  case twistedF4 =>
    exfalso
    have hC : lieOrderCofactor .twistedF4 n (2 ^ f) ≤ (2 ^ f) ^ 16 := by
      generalize 2 ^ f = q at hq ⊢
      show (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤ q ^ 16
      calc (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤ q ^ 7 * q ^ 4 * q ^ 4 * q := by
            gcongr
            · exact pow_add_one_le_pow_succ hq 6
            · exact Nat.sub_le _ _
            · exact pow_add_one_le_pow_succ hq 3
            · exact Nat.sub_le _ _
        _ = q ^ 16 := by ring
    exact false_of_size hq hqN (by simp [lieSylowExponent]) hC hmC hD hm
  case Tits =>
    exfalso
    obtain ⟨-, -, -, -, rfl⟩ := hadm
    simp [lieSylowExponent] at hNf
    omega

end L4Order

theorem eq_psl_four_of_lieModel_two_of_two_le (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hY : LieModel Y t n 2 f)
    {g : ℕ} (hg : 2 ≤ g) (hL : LieModel Y .PSL 4 2 g) : t = .PSL ∧ n = 4 ∧ f = g := by
  have hadm' : StatedLieAdmissible .PSL 4 2 g := hL.admissible
  obtain ⟨-, hM, -⟩ := hO Y t n 2 f hadm hY
  obtain ⟨-, hM', -⟩ := hO Y .PSL 4 2 g hadm' hL
  rw [L4Order.lieOrderDivisor_psl_four (by omega), mul_one,
    L4Order.lieOrderNumerator_psl_four] at hM'
  obtain ⟨hNf, hmC⟩ := L4Order.sylow_and_cofactor hadm (by omega) hM hM'
  exact L4Order.core hadm hg hNf hmC

theorem eq_psl_four_of_lieModel_two (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hY : LieModel Y t n 2 f)
    {i : ℕ} (hi : 1 ≤ i) (hL : LieModel Y .PSL 4 2 (2 ^ i)) : t = .PSL ∧ n = 4 ∧ f = 2 ^ i :=
  eq_psl_four_of_lieModel_two_of_two_le hO hadm hY (L4Order.two_le_two_pow hi) hL

theorem card_alternatingGroup_fin_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 8)
  simp only [Nat.card_perm, Nat.card_fin] at h2
  have h8 : Nat.factorial 8 = 40320 := by decide
  omega

theorem eq_psl_four_one_of_lieModel_two_of_alt8
    (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hY : LieModel Y t n 2 f)
    (hA : Nonempty (Y ≃* alternatingGroup (Fin 8))) : t = .PSL ∧ n = 4 ∧ f = 1 := by
  obtain ⟨e⟩ := hA
  have hcard : Nat.card Y = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin_eight]
  obtain ⟨-, hM, -⟩ := hO Y t n 2 f hadm hY
  rw [hcard] at hM
  have hT := ordProj_two_eq_of_two hadm hM
  rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num, ordProj_two_pow_mul_odd (by decide)] at hT
  have hNf : lieSylowExponent t n * f = 6 := (Nat.pow_right_injective le_rfl hT).symm
  rcases eq_of_sylow_mul_eq_six hadm hNf with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact absurd hM (by decide)
  · exfalso
    exact ((PSL3Four.excludes_alternating_models_stated Y
      (hY.statedClassicalModel_of_ne_zero (by norm_num))).2.2 (Fin 8) (by simp)).false e
  · exact ⟨rfl, rfl, rfl⟩
  · exact absurd hM (by decide)
  · exact absurd hM (by decide)
  · exact absurd hM (by decide)

end CFSG.ComponentClassification.CatFC

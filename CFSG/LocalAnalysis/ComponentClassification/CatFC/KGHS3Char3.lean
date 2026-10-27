module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders

theorem lieMin_le_of_admissible {t : StatedLieTag} {n p f : ℕ}
    (h : StatedLieAdmissible t n p f) : lieMin t ≤ n := by
  obtain ⟨-, -, h⟩ := h
  cases t <;> simp only [StatedLieAdmissible, lieMin] at h ⊢ <;>
    first | omega | exact Nat.zero_le _ | skip

theorem lieOrd_lt_hs_of_char_three {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 3 f) (hmin : lieMin t ≤ n)
    (h3 : (lieOrd t n (3 ^ f)).factorization 3 ≤ 4) (hne : lieOrd t n (3 ^ f) ≠ 0) :
    lieOrd t n (3 ^ f) < 44352000 := by
  have hdvd := pow_lieExp_dvd hmin (3 ^ f)
  have hle : f * lieExp t n ≤ 4 := by
    have h1 : 3 ^ (f * lieExp t n) ∣ lieOrd t n (3 ^ f) := by rw [pow_mul]; exact hdvd
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h1
    omega
  obtain ⟨hp, hf, hrest⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn2, -, hn23⟩ := hrest
    simp only [lieExp] at hle
    have hn : n ≤ 3 := by
      by_contra hcon
      have h12 : 12 ≤ (n - 1) * n := by
        calc 12 = 3 * 4 := by norm_num
          _ ≤ (n - 1) * n := Nat.mul_le_mul (by omega) (by omega)
      have h6 : 6 ≤ (n - 1) * n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
      nlinarith
    have hf4 : f ≤ 4 := by
      have : 1 ≤ (n - 1) * n / 2 := by
        interval_cases n <;> simp
      nlinarith
    interval_cases n <;> interval_cases f <;> first | decide | (exfalso; revert hle; norm_num; done) | (exfalso; revert hn23; norm_num; done) | (exfalso; omega)
  case PSU =>
    obtain ⟨hn3, -⟩ := hrest
    simp only [lieExp] at hle
    have hn : n ≤ 3 := by
      by_contra hcon
      have h12 : 12 ≤ (n - 1) * n := by
        calc 12 = 3 * 4 := by norm_num
          _ ≤ (n - 1) * n := Nat.mul_le_mul (by omega) (by omega)
      have h6 : 6 ≤ (n - 1) * n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
      nlinarith
    have hf4 : f ≤ 4 := by
      have : 1 ≤ (n - 1) * n / 2 := by
        interval_cases n <;> simp
      nlinarith
    interval_cases n <;> interval_cases f <;> first | decide | (exfalso; revert hle; norm_num; done) | (exfalso; omega)
  case PSp =>
    obtain ⟨hn2, -⟩ := hrest
    simp only [lieExp] at hle
    have hn : n ≤ 2 := by
      by_contra hcon
      nlinarith
    have hf4 : f ≤ 4 := by nlinarith
    interval_cases n <;> interval_cases f <;> first | decide | (exfalso; revert hle; norm_num; done) | (exfalso; omega)
  case POmegaOdd =>
    obtain ⟨hn3, -⟩ := hrest
    simp only [lieExp] at hle
    exfalso
    nlinarith
  case POmegaPlus =>
    have hn4 : 4 ≤ n := hrest
    simp only [lieExp] at hle
    exfalso
    have : 12 ≤ n * (n - 1) := by
      calc 12 = 4 * 3 := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn4 (by omega)
    nlinarith
  case POmegaMinus =>
    have hn4 : 4 ≤ n := hrest
    simp only [lieExp] at hle
    exfalso
    have : 12 ≤ n * (n - 1) := by
      calc 12 = 4 * 3 := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn4 (by omega)
    nlinarith
  case G2 => simp only [lieExp] at hle; omega
  case F4 => simp only [lieExp] at hle; omega
  case E6 => simp only [lieExp] at hle; omega
  case E7 => simp only [lieExp] at hle; omega
  case E8 => simp only [lieExp] at hle; omega
  case twistedE6 => simp only [lieExp] at hle; omega
  case trialityD4 => simp only [lieExp] at hle; omega
  case twistedB2 => obtain ⟨-, hp2, -⟩ := hrest; omega
  case twistedG2 =>
    obtain ⟨-, -, ⟨k, hk⟩, hf3⟩ := hrest
    simp only [lieExp] at hle
    omega
  case twistedF4 => obtain ⟨-, hp2, -⟩ := hrest; omega
  case Tits => obtain ⟨-, hp2, -⟩ := hrest; omega

end CFSG.ComponentClassification.CatFC.KGHS3

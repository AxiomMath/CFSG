module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

theorem cl24_D_coprime {τ : StatedLieTag} {n j : ℕ} (hadm : StatedLieAdmissible τ n 3 j) :
    Nat.Coprime (lieOrderDivisor τ n (3 ^ j)) 3 :=
  Nat.Coprime.coprime_dvd_left (lieOrderDivisor_dvd_cofactor hadm)
    (lieOrderCofactor_coprime hadm)

theorem cl24_D_le {τ : StatedLieTag} {n j : ℕ} (hadm : StatedLieAdmissible τ n 3 j) :
    lieOrderDivisor τ n (3 ^ j) ≤ 3 ^ j + 1 := by
  have hj : 1 ≤ j := hadm.2.1
  have h3j : 3 ≤ 3 ^ j := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  cases τ
  case PSL =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_right n (by omega)).trans (by omega)
  case PSU =>
    simp only [lieOrderDivisor]
    exact Nat.gcd_le_right n (by omega)
  case PSp =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_left (3 ^ j - 1) (by norm_num : 0 < 2)).trans (by omega)
  case POmegaOdd =>
    simp only [lieOrderDivisor]
    omega
  case POmegaPlus =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_left ((3 ^ j) ^ n - 1) (by norm_num : 0 < 4)).trans (by omega)
  case POmegaMinus =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_left ((3 ^ j) ^ n + 1) (by norm_num : 0 < 4)).trans (by omega)
  case E6 =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_left (3 ^ j - 1) (by norm_num : 0 < 3)).trans (by omega)
  case E7 =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_left (3 ^ j - 1) (by norm_num : 0 < 2)).trans (by omega)
  case twistedE6 =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_left (3 ^ j + 1) (by norm_num : 0 < 3)).trans (by omega)
  all_goals
    simp only [lieOrderDivisor]
    omega

theorem cl24_D_le_four {τ : StatedLieTag} {n j : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (h1 : τ ≠ .PSL) (h2 : τ ≠ .PSU) : lieOrderDivisor τ n (3 ^ j) ≤ 4 := by
  cases τ
  case PSL => exact absurd rfl h1
  case PSU => exact absurd rfl h2
  case PSp =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_left (3 ^ j - 1) (by norm_num : 0 < 2)).trans (by norm_num)
  case POmegaPlus =>
    simp only [lieOrderDivisor]
    exact Nat.gcd_le_left ((3 ^ j) ^ n - 1) (by norm_num : 0 < 4)
  case POmegaMinus =>
    simp only [lieOrderDivisor]
    exact Nat.gcd_le_left ((3 ^ j) ^ n + 1) (by norm_num : 0 < 4)
  case E6 =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_left (3 ^ j - 1) (by norm_num : 0 < 3)).trans (by norm_num)
  case E7 =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_left (3 ^ j - 1) (by norm_num : 0 < 2)).trans (by norm_num)
  case twistedE6 =>
    simp only [lieOrderDivisor]
    exact (Nat.gcd_le_left (3 ^ j + 1) (by norm_num : 0 < 3)).trans (by norm_num)
  all_goals
    simp only [lieOrderDivisor]
    norm_num

theorem cl24_D_PSL_dvd (n q : ℕ) : lieOrderDivisor .PSL n q ∣ n :=
  Nat.gcd_dvd_left _ _

theorem cl24_D_PSU_dvd (n q : ℕ) : lieOrderDivisor .PSU n q ∣ n :=
  Nat.gcd_dvd_left _ _

theorem cl24_D_PSL_dvd_sub (n q : ℕ) : lieOrderDivisor .PSL n q ∣ q - 1 :=
  Nat.gcd_dvd_right _ _

theorem cl24_prime_dvd_D {τ : StatedLieTag} {n j ℓ : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (hℓ : ℓ.Prime) (h : ℓ ∣ lieOrderDivisor τ n (3 ^ j)) :
    ℓ = 2 ∨ ℓ = 3 ∨ (ℓ ∣ 3 ^ (2 * j) - 1 ∧ (τ = .PSL → 3 ≤ n)) := by
  cases τ
  case PSL =>
    obtain ⟨hn2, -, hn3⟩ := hadm.2.2
    by_cases h2 : n = 2
    · left
      subst n
      simp only [lieOrderDivisor] at h
      have hdvd : ℓ ∣ 2 := Nat.dvd_trans h (Nat.gcd_dvd_left 2 (3 ^ j - 1))
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hdvd
    · right; right
      refine ⟨?_, fun _ => by omega⟩
      simp only [lieOrderDivisor] at h
      have hq : ℓ ∣ 3 ^ j - 1 := Nat.dvd_trans h (Nat.gcd_dvd_right n (3 ^ j - 1))
      have hs : ℓ ∣ (3 ^ j) ^ 2 - 1 := hq.trans (sub_one_dvd_sq_sub_one (3 ^ j))
      rwa [← pow_mul, mul_comm j 2] at hs
  case PSU =>
    right; right
    refine ⟨?_, fun h' => absurd h' (by decide)⟩
    simp only [lieOrderDivisor] at h
    have hq : ℓ ∣ 3 ^ j + 1 := Nat.dvd_trans h (Nat.gcd_dvd_right n (3 ^ j + 1))
    have hs : ℓ ∣ (3 ^ j) ^ 2 - 1 := hq.trans (add_one_dvd_sq_sub_one (3 ^ j))
    rwa [← pow_mul, mul_comm j 2] at hs
  case PSp =>
    left
    simp only [lieOrderDivisor] at h
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1
      (Nat.dvd_trans h (Nat.gcd_dvd_left 2 (3 ^ j - 1)))
  case POmegaOdd =>
    left
    have h2 : ℓ ∣ 2 := by simpa only [lieOrderDivisor] using h
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2
  case POmegaPlus =>
    left
    simp only [lieOrderDivisor] at h
    have h4 : ℓ ∣ 4 := Nat.dvd_trans h (Nat.gcd_dvd_left 4 ((3 ^ j) ^ n - 1))
    have h4' : ℓ ∣ 2 ^ 2 := by simpa using h4
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h4')
  case POmegaMinus =>
    left
    simp only [lieOrderDivisor] at h
    have h4 : ℓ ∣ 4 := Nat.dvd_trans h (Nat.gcd_dvd_left 4 ((3 ^ j) ^ n + 1))
    have h4' : ℓ ∣ 2 ^ 2 := by simpa using h4
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h4')
  case E6 =>
    right; left
    simp only [lieOrderDivisor] at h
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
      (Nat.dvd_trans h (Nat.gcd_dvd_left 3 (3 ^ j - 1)))
  case E7 =>
    left
    simp only [lieOrderDivisor] at h
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1
      (Nat.dvd_trans h (Nat.gcd_dvd_left 2 (3 ^ j - 1)))
  case twistedE6 =>
    right; left
    simp only [lieOrderDivisor] at h
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
      (Nat.dvd_trans h (Nat.gcd_dvd_left 3 (3 ^ j + 1)))
  all_goals
    simp only [lieOrderDivisor] at h
    exact absurd (Nat.dvd_one.mp h) hℓ.ne_one

theorem cl24_E_three_le_or {τ : StatedLieTag} {n j : ℕ} (hadm : StatedLieAdmissible τ n 3 j) :
    3 ≤ cl24E τ n ∨ (τ = .PSL ∧ n = 2) := by
  cases τ
  case PSL =>
    have hn : 2 ≤ n := hadm.2.2.1
    by_cases h2 : n = 2
    · exact Or.inr ⟨rfl, h2⟩
    · exact Or.inl (by simp only [cl24E]; omega)
  case PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    left
    simp only [cl24E]
    split_ifs <;> omega
  case PSp =>
    have hn : 2 ≤ n := hadm.2.2.1
    left; simp only [cl24E]; omega
  case POmegaOdd =>
    have hn : 3 ≤ n := hadm.2.2.1
    left; simp only [cl24E]; omega
  case POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    left; simp only [cl24E]; omega
  case POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    left; simp only [cl24E]; omega
  case Tits =>
    exact absurd hadm.2.2.2.1 (by norm_num)
  all_goals
    left
    simp only [cl24E]
    norm_num

theorem cl24_three_le {τ : StatedLieTag} {n j : ℕ} (hadm : StatedLieAdmissible τ n 3 j) :
    3 ≤ j * cl24E τ n := by
  have hj : 1 ≤ j := hadm.2.1
  rcases cl24_E_three_le_or hadm with hE | ⟨rfl, rfl⟩
  · simpa using Nat.mul_le_mul hj hE
  · have hne : 3 ^ j ≠ 3 := fun h => hadm.2.2.2.2 (by simp [h])
    have hj1 : j ≠ 1 := fun h1 => hne (by rw [h1]; norm_num)
    have hj2 : 2 ≤ j := by omega
    simp only [cl24E]
    omega

end CFSG.OddStandard.SmallF3.HypA2Leaves

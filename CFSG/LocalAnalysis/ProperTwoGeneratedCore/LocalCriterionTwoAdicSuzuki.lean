module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTwoAdicBasic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic

theorem suzuki_involution_count_two_part (a : ℕ) (ha : 1 ≤ a)
    (eps n : ℤ) (heps : eps = -1 ∨ eps = 1) (_hn : 1 ≤ n)
    (hcount : (n : ℚ) - 1 = ((2 : ℚ) ^ (2 * a + 1)) ^ 2 *
      (((((2 : ℚ) ^ (2 * a + 1)) ^ 2 + 1) *
          ((2 : ℚ) ^ (2 * a + 1) - 1)) /
        ((2 : ℚ) ^ (2 * a + 1) + (eps : ℚ) * (2 : ℚ) ^ (a + 1) + 1) + 1)) :
    let q : ℤ := 2 ^ (2 * a + 1)
    let r : ℤ := 2 ^ (a + 1)
    q ^ 2 * r ∣ n - 1 ∧ ¬ 2 * q ^ 2 * r ∣ n - 1 ∧ ¬ q ^ 3 ∣ n - 1 := by
  let q : ℤ := 2 ^ (2 * a + 1)
  let r : ℤ := 2 ^ (a + 1)
  change q ^ 2 * r ∣ n - 1 ∧ ¬ 2 * q ^ 2 * r ∣ n - 1 ∧ ¬ q ^ 3 ∣ n - 1
  obtain ⟨g, hg⟩ : ∃ g : ℕ, a = g + 1 := ⟨a - 1, by omega⟩
  let c : ℤ := 2 ^ g
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hq : q = 8 * c ^ 2 := by
    dsimp [q, c]
    rw [hg, show 2 * (g + 1) + 1 = g * 2 + 3 by omega, pow_add, pow_mul]
    norm_num
    ring
  have hr : r = 4 * c := by
    dsimp [r, c]
    rw [hg, show g + 1 + 1 = g + 2 by omega, pow_add]
    norm_num
    ring
  have hrels : r ^ 2 = 2 * q := by rw [hq, hr]; ring
  have hden : (q : ℚ) + (eps : ℚ) * (r : ℚ) + 1 ≠ 0 := by
    have hcQ : 0 < (c : ℚ) := by exact_mod_cast hcpos
    have hcQone : (1 : ℚ) ≤ c := by exact_mod_cast (show (1 : ℤ) ≤ c by omega)
    have hqQ : (q : ℚ) = 8 * (c : ℚ) ^ 2 := by exact_mod_cast hq
    have hrQ : (r : ℚ) = 4 * (c : ℚ) := by exact_mod_cast hr
    rcases heps with rfl | rfl
    · rw [hqQ, hrQ]
      norm_num
      nlinarith [sq_nonneg ((c : ℚ) - 1)]
    · rw [hqQ, hrQ]
      norm_num
      positivity
  have hepssq : eps ^ 2 = 1 := by rcases heps with rfl | rfl <;> norm_num
  have hqQ : (q : ℚ) = (2 : ℚ) ^ (2 * a + 1) := by simp [q]
  have hrQ : (r : ℚ) = (2 : ℚ) ^ (a + 1) := by simp [r]
  have hquot :
      (((q : ℚ) ^ 2 + 1) * ((q : ℚ) - 1) /
        ((q : ℚ) + (eps : ℚ) * (r : ℚ) + 1) + 1) =
      (q : ℚ) ^ 2 - (eps : ℚ) * (r : ℚ) * ((q : ℚ) - 1) := by
    have hr2Q : (r : ℚ) ^ 2 = 2 * (q : ℚ) := by exact_mod_cast hrels
    have he2Q : (eps : ℚ) ^ 2 = 1 := by exact_mod_cast hepssq
    field_simp
    have hterm : (eps : ℚ) ^ 2 * (r : ℚ) ^ 2 = 2 * (q : ℚ) := by
      rw [he2Q, one_mul, hr2Q]
    nlinarith [hterm]
  have hpolyQ : (n : ℚ) - 1 =
      (q : ℚ) ^ 2 * ((q : ℚ) ^ 2 - (eps : ℚ) * (r : ℚ) * ((q : ℚ) - 1)) := by
    rw [← hqQ, ← hrQ, hquot] at hcount
    exact hcount
  have hpoly : n - 1 = q ^ 2 * (q ^ 2 - eps * r * (q - 1)) := by
    exact_mod_cast hpolyQ
  let b : ℤ := 16 * c ^ 3 - 8 * eps * c ^ 2 + eps
  have hb : Odd b := by
    rcases heps with rfl | rfl
    · refine ⟨8 * c ^ 3 + 4 * c ^ 2 - 1, ?_⟩
      dsimp [b]
      ring
    · refine ⟨8 * c ^ 3 - 4 * c ^ 2, ?_⟩
      dsimp [b]
      ring
  have hfactor : n - 1 = (q ^ 2 * r) * b := by
    rw [hpoly, hq, hr]
    dsimp [b]
    ring
  have hdne : q ^ 2 * r ≠ 0 := by dsimp [q, r]; positivity
  obtain ⟨hd, hnot⟩ := odd_cofactor_divisibility (q ^ 2 * r) b hdne hb
  have hdiv : q ^ 2 * r ∣ n - 1 := by rwa [hfactor]
  have hnond : ¬ 2 * q ^ 2 * r ∣ n - 1 := by
    intro h
    apply hnot
    simpa only [mul_assoc, hfactor] using h
  refine ⟨hdiv, hnond, ?_⟩
  intro h
  apply hnond
  have hdq : 2 * q ^ 2 * r ∣ q ^ 3 := by
    refine ⟨c, ?_⟩
    rw [hq, hr]
    ring
  exact dvd_trans hdq h

end CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic

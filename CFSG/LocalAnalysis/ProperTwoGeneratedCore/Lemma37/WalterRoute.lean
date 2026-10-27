module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherAssembly
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.BenderSuzuki.External
open scoped MatrixGroups

section Arithmetic

theorem three_pow_odd_mod_five (m : ℕ) : 3 ^ (2 * m + 1) % 5 = 2 ∨ 3 ^ (2 * m + 1) % 5 = 3 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem not_five_dvd_ordRee (m : ℕ) : ¬ 5 ∣ ordRee (3 ^ (2 * m + 1)) := by
  have hp : Nat.Prime 5 := by norm_num
  set q := 3 ^ (2 * m + 1) with hq
  have hq5 := three_pow_odd_mod_five m
  rw [← hq] at hq5
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ (by norm_num)
  intro h
  rw [ordRee] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have h3 := hp.dvd_of_dvd_pow h
      rw [hq] at h3
      have := hp.dvd_of_dvd_pow h3
      omega
    · have hmod : (q ^ 3 + 1) % 5 = ((q % 5) ^ 3 % 5 + 1) % 5 := by
        rw [Nat.add_mod, Nat.pow_mod]
      rcases hq5 with h' | h' <;> rw [h'] at hmod <;> norm_num at hmod <;> omega
  · omega

end Arithmetic

end CFSG.ProperTwoGeneratedCore.Lemma37

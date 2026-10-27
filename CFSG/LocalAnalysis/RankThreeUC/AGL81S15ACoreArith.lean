module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreLinMat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore

theorem not_dvd_two_pow_mul_iff {r j w : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ 2 ^ j * w ↔ ¬ r ∣ w := by
  rw [Nat.Prime.dvd_mul hr]
  have : ¬ r ∣ 2 ^ j := fun h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  tauto

theorem drop_iff {r j m A B V : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hrm : r ∣ m) (hA : 0 < A)
    (hB : 0 < B) (hAB : A ∣ B) :
    (¬ r ∣ 2 ^ j * (B / A) ∧ r ∣ m ∧ 4 ≤ m ∧ V ≤ padicValNat r m) ↔
      (padicValNat r A = padicValNat r B ∧ 4 ≤ m ∧ V ≤ padicValNat r m) := by
  rw [not_dvd_two_pow_mul_iff hr.out hr2, ← padicValNat_eq_iff_not_dvd_div hA hB hAB]
  tauto

theorem rkLin_true_eq {m Q r j A B : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hQ : 1 ≤ Q)
    (hrQ : r ∣ Q - 1) (hrm : r ∣ m) (hA : 0 < A) (hB : 0 < B) (hAB : A ∣ B) :
    rkLin m true Q r (2 ^ j * (B / A)) =
      m - 1 - (if padicValNat r A = padicValNat r B ∧ 4 ≤ m ∧
        padicValNat r (Q - 1) ≤ padicValNat r m then 1 else 0) := by
  classical
  unfold rkLin
  rw [if_pos (by simpa using (eP_eq_one_iff hQ).2 hrQ)]
  simp only [if_true]
  exact congrArg (m - 1 - ·) (if_congr (drop_iff hr2 hrm hA hB hAB) rfl rfl)

theorem rkLin_false_eq {m Q r j A B : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hrQ : r ∣ Q + 1) (hrm : r ∣ m) (hA : 0 < A) (hB : 0 < B) (hAB : A ∣ B) :
    rkLin m false Q r (2 ^ j * (B / A)) =
      m - 1 - (if padicValNat r A = padicValNat r B ∧ 4 ≤ m ∧
        padicValNat r (Q + 1) ≤ padicValNat r m then 1 else 0) := by
  classical
  unfold rkLin
  rw [if_pos (by simpa using eM_eq_one_iff.2 hrQ)]
  simp only [Bool.false_eq_true, if_false]
  exact congrArg (m - 1 - ·) (if_congr (drop_iff hr2 hrm hA hB hAB) rfl rfl)

end CFSG.LocalAnalysis.RankThreeUC.S15

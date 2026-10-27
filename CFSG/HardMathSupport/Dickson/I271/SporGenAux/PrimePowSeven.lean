module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PrimePowMod
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.Simproc.Factors
public import Mathlib.Data.Nat.Log

public section

namespace CFSG.HardMathSupport.Dickson.I271

theorem primePow_check_two {p N : ℕ} (hN : N ≠ 0) {L : Finset ℕ} (hL : N.primeFactors = L)
    (hcheck : ∀ q ∈ L, q ≠ p → ∀ k ∈ Finset.Icc 1 (Nat.log 2 N), q ^ k ∣ N → q ^ k % p = 1 →
      q = 2 ∧ ¬ 2 ^ (k + 1) ∣ N) :
    ∀ q k : ℕ, q.Prime → q ≠ p → 0 < k → q ^ k ∣ N → q ^ k % p = 1 →
      q = 2 ∧ ¬ 2 ^ (k + 1) ∣ N := by
  intro q k hq hqp hk hdvd hmod
  have hqL : q ∈ L := by
    rw [← hL, Nat.mem_primeFactors]
    exact ⟨hq, (dvd_pow_self q hk.ne').trans hdvd, hN⟩
  have hle : q ^ k ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdvd
  have hkN : k ≤ Nat.log 2 N := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact (Nat.pow_le_pow_left hq.two_le k).trans hle
  exact hcheck q hqL hqp k (Finset.mem_Icc.2 ⟨hk, hkN⟩) hdvd hmod

theorem primePowOK_seven_98 : PrimePowOK 7 98 := by
  refine primePow_mod_ne_one_of_check (by norm_num) (L := {2, 7})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

theorem primePowOK_seven_2058 : PrimePowOK 7 2058 := by
  refine primePow_mod_ne_one_of_check (by norm_num) (L := {2, 3, 7})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

theorem primePowTwo_seven_1176 : ∀ q k : ℕ, q.Prime → q ≠ 7 → 0 < k → q ^ k ∣ 1176 →
    q ^ k % 7 = 1 → q = 2 ∧ ¬ 2 ^ (k + 1) ∣ 1176 := by
  refine primePow_check_two (by norm_num) (L := {2, 3, 7}) (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

theorem primePowTwo_seven_17640 : ∀ q k : ℕ, q.Prime → q ≠ 7 → 0 < k → q ^ k ∣ 17640 →
    q ^ k % 7 = 1 → q = 2 ∧ ¬ 2 ^ (k + 1) ∣ 17640 := by
  refine primePow_check_two (by norm_num) (L := {2, 3, 5, 7}) (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

end CFSG.HardMathSupport.Dickson.I271

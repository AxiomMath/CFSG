module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PrimePowMod
import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.SuccPred

public section

namespace CFSG.HardMathSupport.Dickson.I271

theorem primePow_mod_ne_one_of_check_log {p N : ℕ} (hN : N ≠ 0) {L : Finset ℕ}
    (hL : N.primeFactors = L)
    (hcheck : ∀ q ∈ L, q ≠ p → ∀ k ∈ Finset.Icc 1 (Nat.log 2 N), q ^ k ∣ N → q ^ k % p ≠ 1) :
    PrimePowOK p N := by
  intro q k hq hqp hk hdvd
  have hqL : q ∈ L := by
    rw [← hL, Nat.mem_primeFactors]
    exact ⟨hq, (dvd_pow_self q hk.ne').trans hdvd, hN⟩
  have hle : q ^ k ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdvd
  have hkN : k ≤ Nat.log 2 N := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact (Nat.pow_le_pow_left hq.two_le k).trans hle
  exact hcheck q hqL hqp k (Finset.mem_Icc.2 ⟨hk, hkN⟩) hdvd

theorem PrimePowOK.of_dvd {p N M : ℕ} (h : PrimePowOK p N) (hM : M ∣ N) : PrimePowOK p M :=
  fun q k hq hqp hk hd => h q k hq hqp hk (hd.trans hM)

end CFSG.HardMathSupport.Dickson.I271

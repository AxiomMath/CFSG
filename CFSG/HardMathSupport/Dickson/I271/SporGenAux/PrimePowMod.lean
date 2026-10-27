module

import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.Simproc.Factors
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.HardMathSupport.Dickson.I271

@[expose] def PrimePowOK (p N : ℕ) : Prop :=
  ∀ q k : ℕ, q.Prime → q ≠ p → 0 < k → q ^ k ∣ N → q ^ k % p ≠ 1

theorem primePow_mod_ne_one_of_check {p N : ℕ} (hN : N ≠ 0) {L : Finset ℕ}
    (hL : N.primeFactors = L)
    (hcheck : ∀ q ∈ L, q ≠ p → ∀ k ∈ Finset.Icc 1 N, q ^ k ∣ N → q ^ k % p ≠ 1) :
    ∀ q k : ℕ, q.Prime → q ≠ p → 0 < k → q ^ k ∣ N → q ^ k % p ≠ 1 := by
  intro q k hq hqp hk hdvd
  have hqL : q ∈ L := by
    rw [← hL, Nat.mem_primeFactors]
    exact ⟨hq, (dvd_pow_self q hk.ne').trans hdvd, hN⟩
  have hle : q ^ k ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdvd
  have hkN : k ≤ N := by
    have : k < q ^ k := Nat.lt_pow_self hq.one_lt
    omega
  exact hcheck q hqL hqp k (Finset.mem_Icc.2 ⟨hk, hkN⟩) hdvd


theorem primePowOK_five_50 : PrimePowOK 5 50 := by
  refine primePow_mod_ne_one_of_check (by norm_num) (L := {2, 5})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

theorem primePowOK_five_300 : PrimePowOK 5 300 := by
  refine primePow_mod_ne_one_of_check (by norm_num) (L := {2, 3, 5})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

theorem primePowOK_five_600 : PrimePowOK 5 600 := by
  refine primePow_mod_ne_one_of_check (by norm_num) (L := {2, 3, 5})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

theorem primePowOK_five_1000 : PrimePowOK 5 1000 := by
  refine primePow_mod_ne_one_of_check (by norm_num) (L := {2, 5})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

theorem primePowOK_five_1500 : PrimePowOK 5 1500 := by
  refine primePow_mod_ne_one_of_check (by norm_num) (L := {2, 3, 5})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

theorem primePowOK_five_3000 : PrimePowOK 5 3000 := by
  refine primePow_mod_ne_one_of_check (by norm_num) (L := {2, 3, 5})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

end CFSG.HardMathSupport.Dickson.I271

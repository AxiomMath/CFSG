module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.NormalizerConj

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank

theorem ringEquiv_eq_one_of_pow_three_pow {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (φ : K ≃+* K) {k : ℕ} (h : φ ^ 3 ^ k = 1) : φ = 1 := by
  induction k generalizing φ with
  | zero => simpa using h
  | succ k ih =>
    apply ringEquiv_eq_one_of_pow_three hK φ
    apply ih (φ ^ 3)
    rw [← pow_mul, ← pow_succ']
    exact h

end CFSG.HardMathSupport.Curtis.UnitaryLevi

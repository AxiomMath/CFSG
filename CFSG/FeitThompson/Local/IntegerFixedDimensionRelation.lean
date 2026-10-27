module

public import CFSG.FeitThompson.Local.SubgroupCoverDimensionCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix Module

variable {p d : ℕ} {A : Type*} [Group A] {ι : Type*} [Fintype ι]

theorem sum_weighted_natCard_mul_finrank_glFixedSpace_eq_zero [Finite A]
    (hp : p.Prime) (hA : ¬ p ∣ Nat.card A) (ρ : A →* GL (Fin d) (ZMod p))
    (B : ι → Subgroup A) [∀ i, DecidablePred (· ∈ B i)] (c : ι → ℤ)
    (hc : ∀ a : A, ∑ i with a ∈ B i, c i = 0) :
    ∑ i, c i * (Nat.card (B i) : ℤ) * (finrank (ZMod p) (glFixedSpace ρ (B i)) : ℤ) = 0 := by
  set D : ℤ := ∑ i, c i * (Nat.card (B i) : ℤ) *
    (finrank (ZMod p) (glFixedSpace ρ (B i)) : ℤ)
  refine Int.eq_zero_of_abs_lt_dvd
    (pow_dvd_sum_weighted_natCard_mul_finrank_glFixedSpace hp hA ρ B c hc
      (e := D.natAbs + 1) (Nat.le_add_left 1 _)) ?_
  have h1 : D.natAbs + 1 < p ^ (D.natAbs + 1) := Nat.lt_pow_self hp.one_lt
  have h2 : (D.natAbs : ℤ) < ((p ^ (D.natAbs + 1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h1.le
  rw [Int.abs_eq_natAbs]
  calc (D.natAbs : ℤ) < ((p ^ (D.natAbs + 1) : ℕ) : ℤ) := h2
    _ = (p : ℤ) ^ (D.natAbs + 1) := by push_cast; ring

end CFSG.FeitThompson

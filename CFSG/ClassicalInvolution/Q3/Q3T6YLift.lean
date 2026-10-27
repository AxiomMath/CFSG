module

public import CFSG.ClassicalInvolution.Q3.Q3T6BOddFix

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3T6B

variable {F : Type} [Group F] [Finite F]

theorem exists_mul_mem_pow_two_eq_one {N : Subgroup F} {h : F} {e : ℕ}
    (hodd : Odd (Nat.card N)) (hh : h ^ 2 ^ e ∈ N) : ∃ n ∈ N, (h * n) ^ 2 ^ e = 1 := by
  set d := orderOf (h ^ 2 ^ e) with hd
  have hdodd : Odd d := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hh)
  have hcop : Nat.Coprime (2 ^ e) d := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hdodd)
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨(h ^ 2 ^ e) ^ (-s), Subgroup.zpow_mem _ hh _, ?_⟩
  have hexp : (1 : ℤ) + ((2 ^ e : ℕ) : ℤ) * (-s) = t * (d : ℤ) := by linear_combination -hst
  have e1 : h * (h ^ 2 ^ e) ^ (-s) = h ^ (t * (d : ℤ)) := by
    rw [← zpow_natCast h (2 ^ e), ← zpow_mul, ← zpow_one_add, hexp]
  have hpow : h ^ ((2 ^ e : ℕ) * d) = 1 := by
    rw [pow_mul]
    exact pow_orderOf_eq_one _
  rw [e1, ← zpow_natCast (h ^ (t * (d : ℤ))) (2 ^ e), ← zpow_mul]
  have : t * (d : ℤ) * ((2 ^ e : ℕ) : ℤ) = ((2 ^ e * d : ℕ) : ℤ) * t := by push_cast; ring
  rw [this, zpow_mul, zpow_natCast, hpow, one_zpow]

end CFSG.ClassicalInvolution.Q3.Q3T6Y

module

public import CFSG.FeitThompson.OddOrder.ShiftedInversionIteration
public import Mathlib.Order.CompletePartialOrder
import CFSG.FeitThompson.OddOrder.NormPointCharacterBound
import CFSG.FeitThompson.OddOrder.CubicNormOnePoint
import CFSG.FeitThompson.OddOrder.LargeDegreeNumericalGap
public import CFSG.FeitThompson.Foundations.FrobeniusNormPrimeDegree

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset

variable {F : Type*} [Field F] {p q m : ℕ}

theorem exists_ne_one_mem_normOneShiftSet_of_config (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hFcard : Nat.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (hcop : Nat.Coprime m (p - 1)) :
    ∃ a ∈ normOneShiftSet F m, a ≠ 1 := by
  obtain ⟨hp5, -, -, hqodd⟩ := odd_of_coprime_pow_sub_one_div_sub_one hp hq hqp (hm ▸ hcop)
  have hq3 := hq.two_le
  have hgeom : m = ∑ i ∈ range q, p ^ i := by rw [hm, Nat.geomSum_eq hp.two_le]
  rcases eq_or_ne q 3 with rfl | hq3'
  ·
    have hm3 : m = 1 + p + p ^ 2 := by rw [hgeom, sum_range_three_pow]
    subst hm3
    exact exists_ne_one_mem_normOneShiftSet hp hFcard
  ·
    have hq5 : 5 ≤ q := by
      rw [Nat.odd_iff] at hqodd
      omega
    have : Finite F := finite_of_natCard_eq_prime_pow hp hFcard
    have hbound := abs_natCard_mul_ncard_normOneShiftSet_sub_sq_le_of_config
      (F := F) hp hq hqp hFcard hm hcop
    have h1 : (1 : ℝ) < ((normOneShiftSet F m).ncard : ℝ) :=
      one_lt_of_abs_mul_sub_geomSum_sq_le hp5 hq5 rfl hgeom hbound
    have h1' : 1 < (normOneShiftSet F m).ncard := by exact_mod_cast h1
    exact (Set.one_lt_ncard_iff_nontrivial_and_finite.mp h1').1.exists_ne 1

theorem exists_ne_one_pow_eq_one_and_two_sub_pow_eq_one_of_config (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hFcard : Nat.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (hcop : Nat.Coprime m (p - 1)) :
    ∃ a : F, a ≠ 1 ∧ a ^ m = 1 ∧ (2 - a) ^ m = 1 := by
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_mem_normOneShiftSet_of_config hp hq hqp hFcard hm hcop
  obtain ⟨h, h'⟩ := mem_normOneShiftSet.mp ha
  exact ⟨a, ha1, h, h'⟩

theorem exists_ne_one_norm_bot_eq_one_of_config (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hFcard : Nat.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (hcop : Nat.Coprime m (p - 1)) :
    haveI : Finite F := finite_of_natCard_eq_prime_pow hp hFcard
    ∃ a : F, a ≠ 1 ∧ Algebra.norm (⊥ : Subfield F) a = 1 ∧
      Algebra.norm (⊥ : Subfield F) (2 - a) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp hFcard
  have : CharP F p := charP_of_natCard_eq_prime_pow hp hFcard
  have hgeom : m = ∑ i ∈ range q, p ^ i := by rw [hm, Nat.geomSum_eq hp.two_le]
  obtain ⟨a, ha1, ha, ha'⟩ :=
    exists_ne_one_pow_eq_one_and_two_sub_pow_eq_one_of_config hp hq hqp hFcard hm hcop
  refine ⟨a, ha1, ?_, ?_⟩ <;> refine Subtype.ext ?_ <;>
    rw [coe_norm_bot_eq_pow_sum p F hFcard, ← hgeom] <;> simpa using ‹_›

end

end CFSG.FeitThompson

module

public import Mathlib.RingTheory.Norm.Defs
public import CFSG.FeitThompson.OddOrder.ShiftedInversionIteration
import CFSG.FeitThompson.OddOrder.BgCubicFamilyRoots
import CFSG.FeitThompson.Foundations.IrreducibleCubicSplitsCubicField

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset Polynomial

variable {p : ℕ} {F : Type*} [Field F]

theorem two_sub_pow_char (hp : p.Prime) [CharP F p] (a : F) : (2 - a) ^ p = 2 - a ^ p := by
  have : Fact p.Prime := ⟨hp⟩
  have : ExpChar F p := ExpChar.prime hp
  rw [sub_pow_char, show (2 : F) = 1 + 1 by norm_num, add_pow_char, one_pow]

theorem two_sub_pow_char_pow (hp : p.Prime) [CharP F p] (a : F) (n : ℕ) :
    (2 - a) ^ p ^ n = 2 - a ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, two_sub_pow_char hp, ← pow_mul, ← pow_succ]

theorem sum_range_three_pow (p : ℕ) : ∑ i ∈ range 3, p ^ i = 1 + p + p ^ 2 := by
  simp [Finset.sum_range_succ]

theorem exists_ne_one_pow_eq_one_and_two_sub_pow_eq_one (hp : p.Prime)
    (hcard : Nat.card F = p ^ 3) :
    ∃ a : F, a ≠ 1 ∧ a ^ (1 + p + p ^ 2) = 1 ∧ (2 - a) ^ (1 + p + p ^ 2) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have hchar : CharP F p := charP_of_natCard_eq_prime_pow hp hcard
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  obtain ⟨c, hc⟩ := exists_bgCubic_zmod_no_root p
  obtain ⟨a, hnotmem, -, -, -, -, hfact⟩ :=
    exists_root_frobenius_orbit (F := F) hcard (bgCubic_monic c) (natDegree_bgCubic c) hc
  set φ := algebraMap (ZMod p) F with hφ
  have h0 : ((bgCubic c).map φ).eval 0 = -1 := by simp
  have h2 : ((bgCubic c).map φ).eval 2 = 1 := by
    have h : ((bgCubic c).map φ).eval (φ 2) = φ ((bgCubic c).eval 2) := by
      rw [eval_map, eval₂_at_apply]
    simpa only [map_ofNat, bgCubic_eval_two, map_one] using h
  rw [hfact, eval_mul, eval_mul, eval_sub, eval_sub, eval_sub, eval_X, eval_C, eval_C,
    eval_C] at h0 h2
  refine ⟨a, fun h => hnotmem (h ▸ one_mem _), ?_, ?_⟩
  · rw [pow_add, pow_add, pow_one]
    linear_combination -h0
  · rw [pow_add, pow_add, pow_one, two_sub_pow_char hp, two_sub_pow_char_pow hp]
    linear_combination h2

theorem exists_ne_one_norm_bot_eq_one (hp : p.Prime) (hcard : Nat.card F = p ^ 3) :
    ∃ a : F, a ≠ 1 ∧ Algebra.norm (⊥ : Subfield F) a = 1 ∧
      Algebra.norm (⊥ : Subfield F) (2 - a) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have : CharP F p := charP_of_natCard_eq_prime_pow hp hcard
  obtain ⟨a, ha1, ha, ha'⟩ := exists_ne_one_pow_eq_one_and_two_sub_pow_eq_one hp hcard
  refine ⟨a, ha1, ?_, ?_⟩ <;>
    refine Subtype.ext ?_ <;>
      rw [coe_norm_bot_eq_pow_sum p F hcard, sum_range_three_pow] <;>
        simpa using ‹_›

theorem exists_ne_one_mem_normOneShiftSet (hp : p.Prime) (hcard : Nat.card F = p ^ 3) :
    ∃ a ∈ normOneShiftSet F (1 + p + p ^ 2), a ≠ 1 := by
  obtain ⟨a, ha1, ha, ha'⟩ := exists_ne_one_pow_eq_one_and_two_sub_pow_eq_one hp hcard
  exact ⟨a, mem_normOneShiftSet.mpr ⟨ha, ha'⟩, ha1⟩

theorem normOneShiftSet_ne_singleton_one (hp : p.Prime) (hcard : Nat.card F = p ^ 3) :
    normOneShiftSet F (1 + p + p ^ 2) ≠ {1} := by
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_mem_normOneShiftSet hp hcard
  intro h
  exact ha1 (by simpa [h] using ha)

end

end CFSG.FeitThompson

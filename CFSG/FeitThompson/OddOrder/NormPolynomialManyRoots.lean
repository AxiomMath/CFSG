module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Set.Card
public import CFSG.FeitThompson.OddOrder.ShiftedInversionIteration
import CFSG.FeitThompson.Foundations.FrobeniusNormPrimeDegree
import CFSG.FeitThompson.OddOrder.MobiusNormIteration

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset Polynomial

variable {p q m : ℕ} {F : Type*} [Field F]

noncomputable def normPoly (p q : ℕ) (a : F) : F[X] :=
  (∏ i ∈ range q, (1 + C ((1 - a) ^ p ^ i) * X)) - 1

theorem normPoly_apply (p q : ℕ) (a : F) :
    normPoly p q a = (∏ i ∈ range q, (1 + C ((1 - a) ^ p ^ i) * X)) - 1 := (rfl)

@[simp] theorem normPoly_zero_exponent (p : ℕ) (a : F) : normPoly p 0 a = 0 := by
  simp [normPoly_apply]

theorem eval_normPoly (p q : ℕ) (a c : F) :
    (normPoly p q a).eval c = (∏ i ∈ range q, (1 + (1 - a) ^ p ^ i * c)) - 1 := by
  rw [normPoly_apply, eval_sub, eval_prod, eval_one]
  simp only [eval_add, eval_one, eval_mul, eval_C, eval_X]

theorem degree_one_add_C_mul_X {c : F} (hc : c ≠ 0) : (1 + C c * X : F[X]).degree = 1 := by
  rw [add_comm, ← C_1]
  exact degree_linear hc

theorem degree_normPolyFactor {a : F} (ha : a ≠ 1) (p i : ℕ) :
    (1 + C ((1 - a) ^ p ^ i) * X : F[X]).degree = 1 :=
  degree_one_add_C_mul_X (pow_ne_zero _ (sub_ne_zero.2 (Ne.symm ha)))

theorem degree_prod_normPolyFactor {a : F} (ha : a ≠ 1) (p q : ℕ) :
    (∏ i ∈ range q, (1 + C ((1 - a) ^ p ^ i) * X) : F[X]).degree = (q : WithBot ℕ) := by
  rw [degree_prod, Finset.sum_congr rfl fun i _ => degree_normPolyFactor ha p i]
  simp

theorem degree_normPoly {a : F} (ha : a ≠ 1) (hq : q ≠ 0) :
    (normPoly p q a).degree = (q : WithBot ℕ) := by
  rw [normPoly_apply, degree_sub_eq_left_of_degree_lt (by
    rw [degree_prod_normPolyFactor ha, degree_one]
    exact_mod_cast Nat.pos_of_ne_zero hq), degree_prod_normPolyFactor ha]

theorem natDegree_normPoly {a : F} (ha : a ≠ 1) (hq : q ≠ 0) :
    (normPoly p q a).natDegree = q :=
  natDegree_eq_of_degree_eq_some (degree_normPoly ha hq)

theorem normPoly_ne_zero {a : F} (ha : a ≠ 1) (hq : q ≠ 0) : normPoly p q a ≠ 0 := by
  intro h
  have hd := degree_normPoly (p := p) (q := q) ha hq
  rw [h, degree_zero] at hd
  exact absurd hd (by simp)

theorem pow_prime_pow_eq_self_of_mem_bot [Fact p.Prime] [CharP F p] {x : F}
    (hx : x ∈ (⊥ : Subfield F)) (i : ℕ) : x ^ p ^ i = x := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_mul, ih, (Subfield.mem_bot_iff_pow_eq_self F p).1 hx]

theorem exists_natCast_eq_of_mem_bot [Fact p.Prime] [CharP F p] {x : F}
    (hx : x ∈ (⊥ : Subfield F)) : ∃ k : ℕ, (k : F) = x := by
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).1 hx
  have h0 : (0 : ℤ) ≤ n % (p : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast (Fact.out : p.Prime).pos.ne')
  refine ⟨(n % (p : ℤ)).toNat, ?_⟩
  have h1 : (((n % (p : ℤ)).toNat : ℕ) : F) = ((n % (p : ℤ) : ℤ) : F) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  rw [h1, ← CharP.intCast_eq_intCast_mod F p, hn]

theorem prod_one_add_pow_mul_eq_pow_geomSum [Fact p.Prime] [CharP F p] {a c : F}
    (hc : c ∈ (⊥ : Subfield F)) :
    (∏ i ∈ range q, (1 + (1 - a) ^ p ^ i * c)) = (1 + c * (1 - a)) ^ ∑ i ∈ range q, p ^ i := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [add_pow_char_pow, one_pow, mul_pow, pow_prime_pow_eq_self_of_mem_bot hc, mul_comm]

theorem eval_normPoly_eq_zero_of_mem_bot [Fact p.Prime] [Finite F] [CharP F p]
    (hq : q.Prime) (hmdef : m = (p ^ q - 1) / (p - 1))
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) {c : F} (hc : c ∈ (⊥ : Subfield F)) :
    (normPoly p q a).eval c = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := exists_natCast_eq_of_mem_bot (p := p) hc
  rw [eval_normPoly, prod_one_add_pow_mul_eq_pow_geomSum hc, ← eq_geomSum_of_eq_div hp hmdef, ← hk]
  have hnorm := mobiusSeq_pow_eq_one (F := F) (ne_zero_of_eq_div hp hq.pos hmdef) hinv ha k
  rw [mobiusSeq_apply] at hnorm
  rw [hnorm, sub_self]

theorem p_le_ncard_setOf_isRoot_normPoly [Fact p.Prime] [Finite F] [CharP F p]
    (hq : q.Prime) (hcard : Nat.card F = p ^ q) (hmdef : m = (p ^ q - 1) / (p - 1))
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) :
    p ≤ {x : F | (normPoly p q a).IsRoot x}.ncard := by
  have hp : p.Prime := Fact.out
  have hsub : ((⊥ : Subfield F) : Set F) ⊆ {x : F | (normPoly p q a).IsRoot x} :=
    fun _ hc => eval_normPoly_eq_zero_of_mem_bot hq hmdef hinv ha hc
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [← Nat.card_coe_set_eq,
    show Nat.card ((⊥ : Subfield F) : Set F) = p from natCard_bot_subfield hp hcard] at h

theorem normPoly_spec_of_config [Fact p.Prime] [Finite F] [CharP F p]
    (hq : q.Prime) (_hqp : q < p) (hcard : Nat.card F = p ^ q)
    (hmdef : m = (p ^ q - 1) / (p - 1)) (_hcop : Nat.Coprime m (p - 1))
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) (ha1 : a ≠ 1) :
    normPoly p q a ≠ 0 ∧ (normPoly p q a).degree = (q : WithBot ℕ) ∧
      ∀ c ∈ (⊥ : Subfield F), (normPoly p q a).IsRoot c :=
  ⟨normPoly_ne_zero ha1 hq.ne_zero, degree_normPoly ha1 hq.ne_zero,
    fun _ hc => eval_normPoly_eq_zero_of_mem_bot hq hmdef hinv ha hc⟩

end

end CFSG.FeitThompson

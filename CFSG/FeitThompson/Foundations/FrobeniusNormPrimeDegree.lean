module

public import Mathlib.FieldTheory.Finite.Trace
public import CFSG.FeitThompson.Representations.TrivialDeterminantKernelAbelianOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset

variable {p q : ℕ} {F : Type*} [Field F]

omit [Field F] in
theorem finite_of_natCard_eq_prime_pow (hp : p.Prime) (h : Nat.card F = p ^ q) : Finite F :=
  Nat.finite_of_card_ne_zero (by rw [h]; exact pow_ne_zero _ hp.pos.ne')

theorem natCard_bot_subfield (hp : p.Prime) (h : Nat.card F = p ^ q) :
    Nat.card (⊥ : Subfield F) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  have : CharP F p := charP_of_natCard_eq_prime_pow hp h
  exact Subfield.card_bot F p

theorem pow_prime_pow_eq_self (hp : p.Prime) (h : Nat.card F = p ^ q) (x : F) : x ^ p ^ q = x := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  have : Fintype F := Fintype.ofFinite F
  rw [← h, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

section
variable (p F) [Fact p.Prime] [Finite F] [CharP F p]

theorem finrank_bot_subfield (h : Nat.card F = p ^ q) :
    Module.finrank (⊥ : Subfield F) F = q := by
  have h2 := Module.natCard_eq_pow_finrank (K := (⊥ : Subfield F)) (V := F)
  rw [Subfield.card_bot F p, h] at h2
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h2).symm

theorem frobeniusEquiv_pow_eq_one (h : Nat.card F = p ^ q) : frobeniusEquiv F p ^ q = 1 := by
  rw [← iterateFrobeniusEquiv_eq_pow]
  ext x
  rw [iterateFrobeniusEquiv_def]
  exact pow_prime_pow_eq_self Fact.out h x

theorem frobeniusEquiv_eq_self_iff_mem_bot {x : F} :
    frobeniusEquiv F p x = x ↔ x ∈ (⊥ : Subfield F) :=
  (Subfield.mem_bot_iff_pow_eq_self F p).symm

theorem fixedPoints_frobeniusEquiv :
    Function.fixedPoints (frobeniusEquiv F p) = ((⊥ : Subfield F) : Set F) := by
  ext x; exact frobeniusEquiv_eq_self_iff_mem_bot p F

theorem coe_norm_bot_eq_pow_sum (h : Nat.card F = p ^ q) (z : F) :
    (Algebra.norm (⊥ : Subfield F) z : F) = z ^ ∑ i ∈ range q, p ^ i := by
  have h2 := FiniteField.algebraMap_norm_eq_pow_sum (⊥ : Subfield F) F z
  rw [finrank_bot_subfield p F h, Subfield.card_bot F p] at h2
  exact h2

theorem coe_norm_bot_eq_prod_pow (h : Nat.card F = p ^ q) (z : F) :
    (Algebra.norm (⊥ : Subfield F) z : F) = ∏ i ∈ range q, z ^ p ^ i := by
  have h2 := FiniteField.algebraMap_norm_eq_prod_pow (⊥ : Subfield F) F z
  rw [finrank_bot_subfield p F h, Subfield.card_bot F p] at h2
  exact h2

omit [Finite F] in
theorem coe_norm_bot_mul (z w : F) :
    (Algebra.norm (⊥ : Subfield F) (z * w) : F)
      = (Algebra.norm (⊥ : Subfield F) z : F) * (Algebra.norm (⊥ : Subfield F) w : F) := by
  rw [map_mul]; push_cast; ring

end

theorem pow_sum_eq_prod_pow (z : F) :
    z ^ (∑ i ∈ range q, p ^ i) = ∏ i ∈ range q, z ^ p ^ i :=
  (Finset.prod_pow_eq_pow_sum _ _ _).symm

theorem mul_pow_sum (z w : F) :
    (z * w) ^ (∑ i ∈ range q, p ^ i)
      = z ^ (∑ i ∈ range q, p ^ i) * w ^ (∑ i ∈ range q, p ^ i) := mul_pow _ _ _

theorem pow_sum_mem_bot (hp : p.Prime) (h : Nat.card F = p ^ q) (z : F) :
    z ^ (∑ i ∈ range q, p ^ i) ∈ (⊥ : Subfield F) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  have : CharP F p := charP_of_natCard_eq_prime_pow hp h
  rw [← coe_norm_bot_eq_pow_sum p F h z]
  exact SetLike.coe_mem _

theorem frobenius_and_norm_of_natCard_eq_prime_pow (hp : p.Prime) (h : Nat.card F = p ^ q) :
    CharP F p ∧ Nat.card (⊥ : Subfield F) = p ∧
      ∃ σ : F ≃+* F, (∀ x : F, σ x = x ^ p) ∧ σ ^ q = 1 ∧
        Function.fixedPoints σ = ((⊥ : Subfield F) : Set F) ∧
        (∀ z : F, z ^ (∑ i ∈ range q, p ^ i) ∈ (⊥ : Subfield F) ∧
          z ^ (∑ i ∈ range q, p ^ i) = ∏ i ∈ range q, z ^ p ^ i) ∧
        ∀ z w : F, (z * w) ^ (∑ i ∈ range q, p ^ i)
          = z ^ (∑ i ∈ range q, p ^ i) * w ^ (∑ i ∈ range q, p ^ i) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  have hchar : CharP F p := charP_of_natCard_eq_prime_pow hp h
  exact ⟨hchar, Subfield.card_bot F p, frobeniusEquiv F p, frobeniusEquiv_def F p,
    frobeniusEquiv_pow_eq_one p F h, fixedPoints_frobeniusEquiv p F,
    fun z => ⟨pow_sum_mem_bot hp h z, pow_sum_eq_prod_pow z⟩, fun z w => mul_pow_sum z w⟩

end

end CFSG.FeitThompson

module

public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

structure UnitaryFieldData (p f : ℕ) (K : Type*) [Field K] : Prop where
  prime : p.Prime
  one_le : 1 ≤ f
  card : Nat.card K = p ^ (2 * f)

namespace UnitaryFieldData

variable {p f : ℕ} {K : Type*} [Field K]

theorem finite (h : UnitaryFieldData p f K) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [h.card]; exact pow_ne_zero _ h.prime.ne_zero)

theorem charP (h : UnitaryFieldData p f K) : CharP K p := by
  have := h.finite
  have := Fintype.ofFinite K
  have : Fact p.Prime := ⟨h.prime⟩
  exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card, h.card])

@[expose] noncomputable def bar (h : UnitaryFieldData p f K) : K →+* K :=
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  iterateFrobenius K p f

theorem bar_apply (h : UnitaryFieldData p f K) (c : K) : h.bar c = c ^ p ^ f := rfl

theorem bar_bar (h : UnitaryFieldData p f K) (c : K) : h.bar (h.bar c) = c := by
  have := h.finite
  have := Fintype.ofFinite K
  rw [bar_apply, bar_apply, ← pow_mul, ← pow_add, ← two_mul, ← h.card, Nat.card_eq_fintype_card,
    FiniteField.pow_card]

theorem exists_bar_ne (h : UnitaryFieldData p f K) : ∃ c : K, h.bar c ≠ c := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  have hq : 1 < p ^ f := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
  by_contra! hc
  have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (Polynomial.X ^ p ^ f - Polynomial.X : Polynomial K) (f := id) Function.injective_id
    (fun a => by simp [← bar_apply h, hc a])
    (by
      rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, ← Nat.card_eq_fintype_card, h.card,
        pow_mul']
      nlinarith)
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  rw [hP, Polynomial.natDegree_zero] at hdeg
  omega

@[expose] noncomputable def fixedField (h : UnitaryFieldData p f K) : Subfield K :=
  h.bar.eqLocusField (RingHom.id K)

@[expose] noncomputable def trace (h : UnitaryFieldData p f K) (c : K) : K := c + h.bar c

@[expose] noncomputable def norm (h : UnitaryFieldData p f K) (c : K) : K := c * h.bar c

@[expose] noncomputable def traceZero (h : UnitaryFieldData p f K) : AddSubgroup K :=
  (AddMonoidHom.id K + h.bar.toAddMonoidHom).ker

theorem mem_fixedField (h : UnitaryFieldData p f K) {c : K} : c ∈ h.fixedField ↔ h.bar c = c :=
  Iff.rfl

theorem mem_traceZero (h : UnitaryFieldData p f K) {c : K} : c ∈ h.traceZero ↔ h.trace c = 0 :=
  Iff.rfl

end UnitaryFieldData

end CFSG.LocalAnalysis.ComponentInitial

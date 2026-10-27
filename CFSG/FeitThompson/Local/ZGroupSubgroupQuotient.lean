module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import CFSG.FeitThompson.Foundations.NilpotentNormalizerCondition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {X : Type*} [Group X]

theorem isZGroup_iff_forall_isCyclic [Finite X] :
    IsZGroup X ↔ ∀ q : ℕ, q.Prime → ∀ Q : Subgroup X,
      Nat.card Q = q ^ (Nat.card X).factorization q → IsCyclic Q := by
  rw [isZGroup_iff]
  refine ⟨fun h q hq Q hQ => ?_, fun h q hq Q => ?_⟩ <;> have : Fact q.Prime := ⟨hq⟩
  · have : IsZGroup X := (isZGroup_iff X).2 h
    exact (IsPGroup.of_card hQ).isCyclic_of_isZGroup
  · exact h q hq Q Q.card_eq_multiplicity

theorem isCyclic_of_natCard_eq_pow_factorization [Finite X] [IsZGroup X] {q : ℕ} (hq : q.Prime)
    {Q : Subgroup X} (hQ : Nat.card Q = q ^ (Nat.card X).factorization q) : IsCyclic Q :=
  isZGroup_iff_forall_isCyclic.1 inferInstance q hq Q hQ

theorem isCyclic_subgroup_of_natCard_eq_pow_factorization [Finite X] [IsZGroup X]
    (Y : Subgroup X) {q : ℕ} (hq : q.Prime) {R : Subgroup Y}
    (hR : Nat.card R = q ^ (Nat.card Y).factorization q) : IsCyclic R :=
  isCyclic_of_natCard_eq_pow_factorization hq hR

theorem isCyclic_quotient_of_natCard_eq_pow_factorization [Finite X] [IsZGroup X]
    (D : Subgroup X) [D.Normal] {q : ℕ} (hq : q.Prime) {R : Subgroup (X ⧸ D)}
    (hR : Nat.card R = q ^ (Nat.card (X ⧸ D)).factorization q) : IsCyclic R :=
  isCyclic_of_natCard_eq_pow_factorization hq hR

theorem isCyclic_of_isZGroup_of_isCentralSeries [Finite X] [IsZGroup X] {S : ℕ → Subgroup X}
    {r : ℕ} (hS : IsCentralSeries S r) : IsCyclic X :=
  have : Group.IsNilpotent X := hS.isNilpotent
  inferInstance

theorem isZGroup_iff_isCyclic_of_isNilpotent [Finite X] [Group.IsNilpotent X] :
    IsZGroup X ↔ IsCyclic X :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

end CFSG.FeitThompson

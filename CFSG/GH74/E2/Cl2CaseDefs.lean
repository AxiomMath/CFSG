module

public import CFSG.GH74.E2.Cl2Cl3Defs

public section

namespace CFSG.GH74.E2

open Subgroup

variable {Q : Type*} [Group Q]

@[expose] def NTypeA (a b : MulAut Q) (N : Subgroup Q) : Prop :=
  (∀ n ∈ N, b n = n) ∧ (∀ n ∈ N, a n = n → n = 1)
@[expose] def NTypeB (a b : MulAut Q) (N : Subgroup Q) : Prop :=
  (∀ n ∈ N, a n = n) ∧ (∀ n ∈ N, b n = n → n = 1)
@[expose] def NTypeP (a b : MulAut Q) (N : Subgroup Q) : Prop :=
  (∀ n ∈ N, a n = b n) ∧ (∀ n ∈ N, a n = n → n = 1)
@[expose] def NTypeM (a b : MulAut Q) (N : Subgroup Q) : Prop :=
  (∀ n ∈ N, a (b n) = n) ∧ (∀ n ∈ N, a n = n → n = 1)

@[expose] def CaseAHyp (Q : Type*) [Group Q] (a b : MulAut Q) (N : Subgroup Q) : Prop :=
  NTypeA a b N ∧ ∀ u ∈ dsub Q, a u * u⁻¹ ∈ N ∧ b u * u⁻¹ ∈ N

@[expose] def CaseBHyp (Q : Type*) [Group Q] (a b : MulAut Q) (N : Subgroup Q) : Prop :=
  NTypeA a b N ∧ (∀ u ∈ dsub Q, b u * (a u)⁻¹ ∈ N) ∧ (∀ u ∈ dsub Q, a u = u → u = 1)

@[expose] def CaseCHyp (Q : Type*) [Group Q] (a b : MulAut Q) (N : Subgroup Q) : Prop :=
  NTypeP a b N ∧ (∀ n ∈ N, (∃ u ∈ dsub Q, n = u * u) → n = 1) ∧
    (∀ u ∈ dsub Q, a u = u → u = 1) ∧ (∀ u ∈ dsub Q, b u = u → u = 1) ∧
      16 ≤ (sqsub (dsub Q)).relIndex (dsub Q)

@[expose] def CaseDHyp (Q : Type*) [Group Q] (a b : MulAut Q) (N : Subgroup Q) : Prop :=
  NTypeP a b N ∧ (∀ n ∈ N, ∃ u ∈ dsub Q, n = u * u) ∧
    (∀ u ∈ dsub Q, a u = u → u = 1) ∧ (∀ u ∈ dsub Q, b u = u → u = 1) ∧
      16 ≤ (sqsub (dsub Q)).relIndex (dsub Q)

end CFSG.GH74.E2

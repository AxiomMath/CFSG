module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Descend

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def D4NoCfg : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ (A : Subgroup (MulAut (adjointGroup Tag.D4 K)))
    (ψ : MulAut (adjointGroup Tag.D4 K)) (J : Subgroup (adjointGroup Tag.D4 K)) (q : ℕ),
    S1431Cfg (adjointGroup Tag.D4 K) A ψ J q → (∃ q0 : ℕ, 4 ≤ q0 ∧ q = q0 ^ 3) →
      ψ ∈ inner (adjointGroup Tag.D4 K) →
      (∀ a ∈ A, a ∈ innAutDerived (adjointGroup Tag.D4 K)) → False

end CFSG.HardMathSupport.Dickson.Sec6.I1431

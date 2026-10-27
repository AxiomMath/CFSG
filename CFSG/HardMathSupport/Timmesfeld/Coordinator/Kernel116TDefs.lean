module

public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open

@[expose] def Kernel11_6T : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J → CFSG.Open.IsKGroup J →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ U : Subgroup J, U ≤ Subgroup.center J ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2) →
        ∀ φ : MulAut J, IsPGroup p (Subgroup.zpowers φ) → ∃ x : J, φ = MulAut.conj x

end CFSG.HardMathSupport.Timmesfeld.Coordinator

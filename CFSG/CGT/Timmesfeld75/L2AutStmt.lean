module

public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

@[expose] def AutInvolDichotomy : Prop :=
  ∀ (Q : Type) [Group Q] (S S' : Subgroup Q) (q : ℕ), IsL2Pair Q S q →
    (∃ g : Q, S' = conjSubgroup g S) → S' ≠ S →
    ∀ φ : Q ≃* Q, (∀ x, φ (φ x) = x) → S.map φ.toMonoidHom = S → S'.map φ.toMonoidHom = S' →
      (∀ x, φ x = x) ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (e : Q ≃* SL(2, F)) (σ : F ≃+* F), σ ≠ RingEquiv.refl F ∧
          S.map e.toMonoidHom = utri F ∧ S'.map e.toMonoidHom = ltri F ∧
          ∀ x, e (φ x) = Matrix.SpecialLinearGroup.map (σ : F →+* F) (e x)

end CFSG.CGT.Timmesfeld75

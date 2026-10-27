module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

@[expose] def L2Aut3Classification : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (β : MulAut (StatedProj (StatedSL 2 F))), β ^ 3 = 1 →
    β = 1 ∨ Group.IsSolvable ↥(fixSub β) ∨
      ∃ (σ : F ≃+* F) (φ γ : MulAut (StatedProj (StatedSL 2 F))),
        IsEntrywiseAutPSLn 2 σ φ ∧ β = γ * φ * γ⁻¹

@[expose] def L2FieldFixed : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (β : MulAut (StatedProj (StatedSL 2 F))), β ^ 3 = 1 → β ≠ 1 →
    ∀ (σ : F ≃+* F) (φ γ : MulAut (StatedProj (StatedSL 2 F))),
      IsEntrywiseAutPSLn 2 σ φ → β = γ * φ * γ⁻¹ →
        ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F = Nat.card F₀ ^ 3 ∧
          Nonempty (↥(fixSub β) ≃* StatedProj (StatedSL 2 F₀))

@[expose] def L2CentreThree : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → IsPGroup 3 (Subgroup.center Q) →
    Subgroup.center Q ≠ ⊥ → ∀ (F : Type) [Field F] [Finite F],
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* StatedProj (StatedSL 2 F)) → Nat.card F = 9

end CFSG.HardMathSupport.Solomon.Coordinator

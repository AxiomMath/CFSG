module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25Up
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Two
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def Up34Pumpup (S : Type) [Group S] (α : MulAut S) : Prop :=
  α ^ 3 = 1 ∧ α ≠ 1 ∧ ∃ I : Subgroup S, GLAPComponent 3 (fixSubgroup α) I ∧
    IsLThreeFour (↥I ⧸ GLAPPrimeCore 3 ↥I)

@[expose] def Up34AltLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 5 ≤ n → Nonempty (S ≃* alternatingGroup (Fin n)) →
    ∀ α : MulAut S, ¬ Up34Pumpup S α

@[expose] def Up34SporLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ name : TauCeti.SporadicName,
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      ∀ α : MulAut S, ¬ Up34Pumpup S α

@[expose] def Up34OddLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, ¬ IsCharTwoLieIndex d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, ¬ Up34Pumpup S α

@[expose] def Up34Chev2Leaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevTwo S → ∀ α : MulAut S, Up34Pumpup S α →
      IsCatalogLieIso S IsL364Index ∨ IsCatalogLieIso S Is3D44Index ∨
        IsCatalogLieIso S IsD44Index

@[expose] def Up34D44Centre : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    IsCatalogLieIso (Q ⧸ Subgroup.center Q) IsD44Index → Subgroup.center Q = ⊥

@[expose] def Up34L364NotInnDiag : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    IsCatalogLieIso (Q ⧸ Subgroup.center Q) IsL364Index →
    ∀ β : MulAut Q, Up34Pumpup Q β → ¬ IsInnDiagThree β

@[expose] def Up34Concl (Q : Type) [Group Q] (β : MulAut Q) : Prop :=
  (IsCatalogLieIso (Q ⧸ Subgroup.center Q) IsL364Index ∧ ¬ IsInnDiagThree β) ∨
    IsCatalogLieIso (Q ⧸ Subgroup.center Q) Is3D44Index ∨
    (IsCatalogLieIso Q IsD44Index ∧ Subgroup.center Q = ⊥)

@[expose] def Up34Core : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → CFSG.Open.IsKGroup Q →
    GLAPPrimeCore 3 Q = ⊥ → ∀ β : MulAut Q, Up34Pumpup Q β → Up34Concl Q β

end CFSG.HardMathSupport.Dickson.Sec6

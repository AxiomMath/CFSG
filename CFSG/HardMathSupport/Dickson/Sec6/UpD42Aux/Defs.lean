module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25Two
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Up
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal

@[expose] def IsD42Index : TauCeti.LieTypeIndex → Prop
  | .D r q => r = 4 ∧ q.p = 2 ∧ q.exponent = 1
  | _ => False

@[expose] def IsOmegaTwoBigIndex : TauCeti.LieTypeIndex → Prop
  | .D r q => 5 ≤ r ∧ q.p = 2 ∧ q.exponent = 1
  | .twistedD r q => 5 ≤ r ∧ q.p = 2 ∧ q.exponent = 1
  | _ => False

@[expose] def IsTwE62Index : TauCeti.LieTypeIndex → Prop
  | .twistedE6 q => q.p = 2 ∧ q.exponent = 1
  | _ => False

@[expose] def IsD48Index : TauCeti.LieTypeIndex → Prop
  | .D r q => r = 4 ∧ q.p = 2 ∧ q.exponent = 3
  | _ => False

@[expose] def UpD42Pumpup (S : Type) [Group S] (α : MulAut S) : Prop :=
  α ^ 3 = 1 ∧ α ≠ 1 ∧ ∃ I : Subgroup S, GLAPComponent 3 (fixSubgroup α) I ∧
    IsCatalogLieIso (↥I ⧸ GLAPPrimeCore 3 ↥I) IsD42Index

@[expose] def UpD42AltLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 5 ≤ n → Nonempty (S ≃* alternatingGroup (Fin n)) →
    ∀ α : MulAut S, ¬ UpD42Pumpup S α

@[expose] def UpD42SporLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Open.IsKGroup S → ∀ name : TauCeti.SporadicName,
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      ∀ α : MulAut S, ¬ UpD42Pumpup S α

@[expose] def UpD42OddLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, ¬ IsCharTwoLieIndex d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, ¬ UpD42Pumpup S α

@[expose] def UpD42Chev2Leaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevTwo S → ∀ α : MulAut S, UpD42Pumpup S α →
      IsCatalogLieIso S IsOmegaTwoBigIndex ∨ IsCatalogLieIso S IsTwE62Index ∨
        IsCatalogLieIso S IsD48Index

@[expose] def UpD42Concl (Q : Type) [Group Q] : Prop :=
  IsCatalogLieIso (Q ⧸ Subgroup.center Q) IsOmegaTwoBigIndex ∨
    IsCatalogLieIso (Q ⧸ Subgroup.center Q) IsTwE62Index ∨
    IsCatalogLieIso (Q ⧸ Subgroup.center Q) IsD48Index

@[expose] def UpD42Core : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → CFSG.Open.IsKGroup Q →
    GLAPPrimeCore 3 Q = ⊥ → ∀ β : MulAut Q, UpD42Pumpup Q β → UpD42Concl Q

@[expose] def UpD42Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G), CFSG.IsKGroup ↥X →
    GLAPComponent 3 X K → ∀ b : G, b ∈ X → b ∈ Subgroup.normalizer (K : Set G) →
    b ^ 3 = 1 → b ∉ dQ K → ∀ J : Subgroup G,
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J →
    IsCatalogLieIso (↥J ⧸ GLAPPrimeCore 3 ↥J) IsD42Index →
      UpD42Concl (barOf 3 K)

end CFSG.HardMathSupport.Dickson.Sec6

end

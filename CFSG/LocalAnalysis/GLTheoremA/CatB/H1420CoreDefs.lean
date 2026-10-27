module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def I1420Target (p z : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (p = 3 ∧ z = 3 ∧ s = .Fi24Prime) ∨ (p = 5 ∧ z = 1 ∧ s = .HN)

@[expose] def I1420Core (p z : ℕ) (s : TauCeti.SporadicName) {S : Type} [Group S] [Finite S]
    (β : MulAut S) (J : Subgroup S) : Prop :=
  IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧ β ^ p = 1 ∧ β ≠ 1 ∧ J ≠ ⊤ ∧
    GLAPComponent p (fixSubgroup β) J ∧
    Nonempty (PSimple p J ≃* (TauCeti.CFSGIndex.sporadic s).Group) ∧
    Nat.card (Subgroup.center (PQuot p J)) ∣ z

@[expose] def I1420Lie : Prop :=
  ∀ (p z : ℕ) (s : TauCeti.SporadicName), I1420Target p z s →
    ∀ (S : Type) [Group S] [Finite S] (idx : TauCeti.ValidLieTypeIndex),
      S ≃* (TauCeti.CFSGIndex.lie idx).Group → ∀ (β : MulAut S) (J : Subgroup S),
        I1420Core p z s β J → False

@[expose] def I1420Alt : Prop :=
  ∀ (p z : ℕ) (s : TauCeti.SporadicName), I1420Target p z s →
    ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 5 ≤ n → S ≃* alternatingGroup (Fin n) →
      ∀ (β : MulAut S) (J : Subgroup S), I1420Core p z s β J → False

@[expose] def I1420Spor : Prop :=
  ∀ (p z : ℕ) (s : TauCeti.SporadicName), I1420Target p z s →
    ∀ (S : Type) [Group S] [Finite S] (t : TauCeti.SporadicName),
      S ≃* (TauCeti.CFSGIndex.sporadic t).Group → ∀ (β : MulAut S) (J : Subgroup S),
        I1420Core p z s β J → t = .M

end CFSG.LocalAnalysis.GLTheoremA.H1420

end

module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def KDOutChevCentre : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), d.1.characteristic = 3 →
    S ≃* (TauCeti.CFSGIndex.lie d).Group → ∀ β : MulAut S, β ^ 3 = 1 → β ∉ inner S →
      ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup β) J → Subgroup.center (PQuot 3 J) = ⊥

end CFSG.LocalAnalysis.GLTheoremA

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def I1420CoreP (p : ℕ) (P : TauCeti.CFSGIndex → Prop) (z : ℕ) {S : Type} [Group S]
    [Finite S] (β : MulAut S) (J : Subgroup S) : Prop :=
  IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧ β ^ p = 1 ∧ β ≠ 1 ∧ J ≠ ⊤ ∧
    GLAPComponent p (fixSubgroup β) J ∧ catalogIs (PSimple p J) P ∧
    Nat.card (Subgroup.center (PQuot p J)) ∣ z

end CFSG.LocalAnalysis.GLTheoremA.H1420

end

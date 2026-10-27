module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def isL2three6 : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .A 1 q => q.card = 729
    | _ => False

@[expose] def CompOfType (S : Type) [Group S] (α : MulAut S) (T : TauCeti.CFSGIndex → Prop) :
    Prop :=
  ∃ J : Subgroup S,
    GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) J ∧
      catalogIs (PSimple 3 J) T

@[expose] def LieSTypeChar : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (r : ℕ), catalogIs X S8.L84.isType1430 → IsChevSimple r X →
    (r = 2 ∧ (catalogIs X S9.isSp6two ∨ catalogIs X S8.L84.isSp48)) ∨
      (r = 3 ∧ catalogIs X isL2three6)

@[expose] def LieS3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ^ 3 = 1 → α ≠ 1 → CompOfType S α isL2three6 → isL2three18 (.lie d)

@[expose] def LieSInn : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∈ innAutDerived S → α ^ 3 = 1 → α ≠ 1 →
        (CompOfType S α S9.isSp6two → KD264Lie.fieldSize d.1 = 2) ∧
        (CompOfType S α S8.L84.isSp48 →
          KD264Lie.fieldSize d.1 = 2 ∨ KD264Lie.fieldSize d.1 = 8)

@[expose] def LieSOut : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∉ innAutDerived S → α ^ 3 = 1 →
        (CompOfType S α S9.isSp6two → isSp68 (.lie d)) ∧
        (CompOfType S α S8.L84.isSp48 → isSp492 (.lie d))

@[expose] def LieSTwo : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ → RkY Y →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 → KD264Lie.fieldSize d.1 = 2 →
      Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut (Y ⧸ Subgroup.center Y), α ∈ innAutDerived (Y ⧸ Subgroup.center Y) →
        α ^ 3 = 1 → α ≠ 1 →
        (CompOfType (Y ⧸ Subgroup.center Y) α S9.isSp6two →
          S8.L84.isSp82 (.lie d) ∨ isF4two (.lie d)) ∧
        ¬ CompOfType (Y ⧸ Subgroup.center Y) α S8.L84.isSp48

@[expose] def LieSEight : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ → RkY Y →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 → KD264Lie.fieldSize d.1 = 8 →
      Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ ξ : MulAut Y, ξ ^ 3 = 1 → ξ ≠ 1 →
        inducedAut ξ ∈ innAutDerived (Y ⧸ Subgroup.center Y) →
        ∀ J : Subgroup Y,
          GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup ξ) J →
          catalogIs (PSimple 3 J) S8.L84.isSp48 →
          (∃ τ : MulAut Y, τ ^ 3 = 1 ∧ Commute τ ξ ∧ ¬ InnerOnMod 3 J τ ∧ RkTau τ) →
          isSp68 (.lie d)

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end

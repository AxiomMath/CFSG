module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd)
open CFSG.HardMathSupport.Dickson.Sec6 (FamF4 FamE6 FamTwE6 FamE7 FamE8)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def ThreeFreeMult (H : Type) [Group H] : Prop :=
  ∀ (M : Type) [Group M] [Finite M], CFSG.Open.IsQuasisimple M →
    Nonempty (M ⧸ Subgroup.center M ≃* H) → Nat.Coprime 3 (Nat.card ↥(Subgroup.center M))

@[expose] def SmallConcl {S : Type} [Group S] (I : Subgroup S) : Prop :=
  Subgroup.center ↥I = ⊥ ∧ (Nat.card (↥I ⧸ Subgroup.center ↥I) = 360 →
    ∃ H : Subgroup S, I ≤ H ∧ IsSimpleGroup ↥H ∧ ThreeFreeMult ↥H)

@[expose] def SmallFam (Fam : GLALabel → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (labK : GLALabel) (α : MulAut S) (I : Subgroup S),
    Fam labK → Subgroup.center S = ⊥ → α ^ 3 = 1 → α ≠ 1 → InnDiagKind S labK α →
      CFSG.Open.IsComponentOf I (fixSubgroup α) → SmallOrd I → SmallConcl I

@[expose] def SmallExcRes : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : ValidLieTypeIndex),
    (FamF4 d.1 ∨ FamE6 d.1 ∨ FamTwE6 d.1 ∨ FamE7 d.1 ∨ FamE8 d.1) → d.1.characteristic = 2 →
    (S ≃* (CFSGIndex.lie d).Group) → ∀ α : MulAut S, α ∈ innAutDerived S → α ^ 3 = 1 → α ≠ 1 →
      ∀ I : Subgroup S, CFSG.Open.IsComponentOf I (fixSubgroup α) → ¬ SmallOrd I

@[expose] def SmallCentreS : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple 2 S → ∀ (labK : GLALabel) (A : Subgroup (MulAut S)),
      CFSG.Assembly.IsElemAbelian 3 A → 27 ≤ Nat.card ↥A → (∀ β ∈ A, InnDiagKind S labK β) →
      ∀ α ∈ A, α ≠ 1 → ∀ I : Subgroup S, CFSG.Open.IsComponentOf I (fixSubgroup α) →
        SmallOrd I → SmallConcl I

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end

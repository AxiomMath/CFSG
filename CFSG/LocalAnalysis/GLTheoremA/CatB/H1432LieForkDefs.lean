module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def OuterShapeThree (t : StatedLieTag) (n f : ℕ) (t' : StatedLieTag) (n' f' : ℕ) :
    Prop :=
  (t ≠ .trialityD4 ∧ t' = t ∧ n' = n ∧ 3 * f' = f) ∨
    (t = .POmegaPlus ∧ n = 4 ∧ t' = .G2 ∧ n' = 0 ∧ f' = f) ∨
    (t = .POmegaPlus ∧ n = 4 ∧ t' = .trialityD4 ∧ n' = 0 ∧ 3 * f' = f) ∨
    (t = .trialityD4 ∧ t' = .G2 ∧ n' = 0 ∧ f' = f)

@[expose] def OuterLayerThree (t : StatedLieTag) (n f : ℕ) (X : Type) [Group X] : Prop :=
  (∃ (t' : StatedLieTag) (n' f' : ℕ), OuterShapeThree t n f t' n' f' ∧
      CFSG.Blueprint.LieModel X t' n' 3 f') ∨
    (t = .twistedG2 ∧ f = 3 ∧ Nat.card X ∣ 1512)

@[expose] def OuterSubThree (t : StatedLieTag) (n f : ℕ) {Y : Type} [Group Y] (D : Subgroup Y) :
    Prop :=
  ∀ A : Subgroup Y, GLAPComponent 3 D A → OuterLayerThree t n f (PSimple 3 A)

@[expose] def LieOuterThreeAt (Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n 3 f →
    Fam t n 3 f → CFSG.Blueprint.LieModel P t n 3 f →
    ∀ ψ : MulAut P, ψ ^ 3 = 1 → ψ ∉ inner P → OuterSubThree t n f (fixSubgroup ψ)

@[expose] def LieOuterThree : Prop :=
  LieOuterThreeAt fun _ _ _ _ => True

end CFSG.LocalAnalysis.GLTheoremA.H1420

end

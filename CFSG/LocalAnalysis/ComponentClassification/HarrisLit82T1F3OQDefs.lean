module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

namespace F3FG

@[expose] def Harris82OutQuatThreeOrth : Prop :=
  ∀ (S : Type) [Group S] (t : StatedLieTag) (n f : ℕ),
    (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) → 3 ∣ f →
    Blueprint.LieModel S t n 3 f → (∀ f : ℕ, ¬ Blueprint.LieModel S .PSL 2 3 f) →
    (∀ f : ℕ, ¬ Blueprint.LieModel S .POmegaPlus 4 3 f) →
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nonempty (X ⧸ center X ≃* S) →
    ∀ (R : Subgroup (MulAut X)) (φ : ↥R →* PSL(2, ZMod 3)), Function.Surjective φ →
      ∃ r : ↥R, (r : MulAut X) ∈ (MulAut.conj : X →* MulAut X).range ∧ φ r ≠ 1

end F3FG

end CFSG.ComponentClassification.HarrisLit.T1

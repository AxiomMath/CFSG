module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup CFSG.Blueprint CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def Cl24FieldRel (c d : ℕ) : Prop :=
  c = 2 * d ∨ d = c ∨ d = 2 * c ∨ d = 4 * c ∨ d = 3 * c

@[expose] def Cl24TrackedFamily (τ : StatedLieTag) : Prop :=
  ∀ (J : Type) [Group J] (n f : ℕ), StatedLieAdmissible τ n 3 f → LieModel J τ n 3 f →
    ∀ α : MulAut J, orderOf α = 2 → ∀ K : Subgroup (fixedSubgroup α), IsComponent K →
      (∃ (τ' : StatedLieTag) (n' f' : ℕ), Cl24FieldRel f f' ∧ StatedLieAdmissible τ' n' 3 f' ∧
          LieModel (K ⧸ center K) τ' n' 3 f') ∨
        (LieModel J .G2 0 3 1 ∧ α ∉ (MulAut.conj : J →* MulAut J).range ∧
          LieModel K .PSL 2 2 3)

@[expose] def Cl24FieldUnique3 : Prop :=
  ∀ (Q : Type) [Group Q] (τ τ' : StatedLieTag) (n n' j d : ℕ),
    LieModel Q τ n 3 j → LieModel Q τ' n' 3 d → j = d

theorem cl24_tracked_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n f : ℕ, ¬ StatedLieAdmissible τ n 3 f) : Cl24TrackedFamily τ :=
  fun _ _ n f hadm => absurd hadm (hτ n f)

theorem cl24_tracked_twistedB2 : Cl24TrackedFamily .twistedB2 :=
  cl24_tracked_of_not_admissible fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)

theorem cl24_tracked_twistedF4 : Cl24TrackedFamily .twistedF4 :=
  cl24_tracked_of_not_admissible fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)

theorem cl24_tracked_Tits : Cl24TrackedFamily .Tits :=
  cl24_tracked_of_not_admissible fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)

end CFSG.OddStandard.SmallF3.HypA2Leaves

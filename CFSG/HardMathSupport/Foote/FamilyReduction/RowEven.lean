module

public import CFSG.HardMathSupport.Foote.FamilyReduction.Abstract
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenInner

public section

namespace CFSG.HardMathSupport.Foote.FamilyReduction

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification


theorem not_comp5_evenLie {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hna : ∃ x y : Q, x * y ≠ y * x) {τ : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible τ n 2 f) (hQ : LieModel Q τ n 2 f) : ¬ CompIn5 Q := by
  rintro ⟨α, w, hαw, hα, K, hK, -, -⟩
  exact SeitzReduction.F4Pilot.false_of_isComponent_fixedSubgroup_inner hna
    (CatLeaf.involutionCentralizersComponentFree_of_evenLieType ⟨τ, n, f, hadm, hQ⟩) hα
    ⟨w, hαw.symm⟩ hK

end CFSG.HardMathSupport.Foote.FamilyReduction

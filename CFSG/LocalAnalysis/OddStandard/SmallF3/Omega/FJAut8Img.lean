module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelFamily
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelImage

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Assembly.LowTwoRank CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial

private theorem fj_irreducible_zmod_three : ∀ s : ZMod 3, s ^ 2 + 0 * s + 1 ≠ 0 := by decide

theorem fj_matrixProjectiveImage_eight_minus (hn : 1 ≤ 4) :
    matrixProjectiveImage (coordinateQuadMinus 4 (ZMod 3) hn 0 1) = ⊤ := by
  have hZ : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus 4 (ZMod 3) 0 1)))
      .POmegaMinus 4 3 1 :=
    ⟨by unfold StatedLieAdmissible; decide, ZMod 3, inferInstance, inferInstance,
      by simp, 0, 1, fj_irreducible_zmod_three, ⟨MulEquiv.refl _⟩⟩
  rw [← ((orthogonal_geometry_model_stabilizer_preserving_image _ .POmegaMinus
    (.inr (.inr rfl)) 4 3 1 hZ) hn (ZMod 3) (by simp) 0 1 fj_irreducible_zmod_three
    (MulEquiv.refl _)).1]
  exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant _
    .POmegaMinus (.inr rfl) 4 3 1 hZ) hn (ZMod 3) (by simp) 0 1
    fj_irreducible_zmod_three).2

end CFSG.OddStandard.SmallF3.Omega

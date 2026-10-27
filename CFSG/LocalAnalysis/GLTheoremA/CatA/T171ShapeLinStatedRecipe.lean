module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLinTrans
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial

@[expose] noncomputable def statedRecipeEquiv (n : ℕ) (K : Type) [Field K] :
    LinearFlag.projectiveSL n K ≃* LargeEvenProj (StatedSL n K) :=
  QuotientGroup.congr (LinearFlag.scalars n K)
    ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K)
    (by
      rw [LinearFlag.scalars_eq_center]
      exact CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars n K)

theorem statedRecipeEquiv_proj (n : ℕ) (K : Type) [Field K]
    (A : Matrix.SpecialLinearGroup (Fin n) K) :
    statedRecipeEquiv n K (LinearFlag.proj n K A) =
      LargeEvenProjMk (StatedSL n K)
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K A) :=
  QuotientGroup.congr_mk _ _ _ _ A

theorem statedProjConj_recipe {N : ℕ} {K : Type} [Field K] (B : GL (Fin N) K)
    (hB : B ∈ Subgroup.normalizer (StatedSL N K : Set (GL (Fin N) K))) :
    MulAut.congr (statedRecipeEquiv N K).symm
      (TableB.projConj (StatedSL N K) ⟨B, hB⟩) = LinearFlag.conjAut N K B := by
  ext x
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective N K x
  show (statedRecipeEquiv N K).symm
      (TableB.projConj (StatedSL N K) ⟨B, hB⟩
        ((statedRecipeEquiv N K) (LinearFlag.proj N K g))) =
    LinearFlag.conjAut N K B (LinearFlag.proj N K g)
  rw [statedRecipeEquiv_proj]
  rw [show LargeEvenProjMk (StatedSL N K)
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL N K g) =
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL N K g : StatedSL N K) :
        LargeEvenProj (StatedSL N K)) from rfl,
    TableB.projConj_mk]
  rw [show ((StatedSL N K).normalizerMonoidHom ⟨B, hB⟩)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL N K g) =
      CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL N K
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B g) by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
      show ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL N K g : StatedSL N K) :
          GL (Fin N) K) = Matrix.SpecialLinearGroup.toGL g from rfl,
      show ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL N K
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B g) :
          StatedSL N K) : GL (Fin N) K) =
        Matrix.SpecialLinearGroup.toGL
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B g)
        from rfl,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]]
  rw [show ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL N K
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B g) :
        StatedSL N K) : LargeEvenProj (StatedSL N K)) =
      LargeEvenProjMk (StatedSL N K)
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL N K
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B g))
      from rfl,
    ← statedRecipeEquiv_proj, MulEquiv.symm_apply_apply, LinearFlag.conjAut_proj]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

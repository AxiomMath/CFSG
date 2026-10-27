module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitComponentsProduct
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourSplitComponents

open CatalogueBOrthogonalFourSplit

universe u

variable {K : Type u} [Field K]

@[expose] def specialLinearCover :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      specialImage K :=
  (specialRho (K := K)).rangeRestrict

theorem specialLinearCover_surjective :
    Function.Surjective (specialLinearCover (K := K)) :=
  (specialRho (K := K)).rangeRestrict_surjective

theorem specialLinearCover_kernel_central :
    (specialLinearCover (K := K)).ker ≤
      Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro z hz
  apply specialRho_kernel_le_center
  change specialRho z = 1
  exact congrArg Subtype.val (show specialLinearCover z = 1 from hz)

variable [Finite K]

instance determinantIsometriesFinite : Finite (DeterminantIsometries K) := by
  apply Finite.of_injective
    (fun g : DeterminantIsometries K =>
      (g.val : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K))
  intro g h heq
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  exact congrFun heq X

theorem specialImage_pComponent_quasisimple (p : ℕ) [Fact p.Prime]
    (L : Subgroup (specialImage K)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  let f := specialLinearCover (K := K)
  obtain ⟨J, hJ, hmap, _⟩ := CatalogueBCentralQuotient.pComponent_exists_lift p f
    specialLinearCover_surjective specialLinearCover_kernel_central L hL
  have hquasi := (CatalogueBCentralQuotient.pComponent_quasisimple_iff f
    specialLinearCover_kernel_central p J hJ).mp
      (specialLinearProduct_pComponent_quasisimple p J hJ)
  exact hmap ▸ hquasi

theorem determinant_pComponent_quasisimple (p : ℕ) [Fact p.Prime]
    (L : Subgroup (DeterminantIsometries K)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L :=
  CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient
    p (specialImage K) (specialImage_pComponent_quasisimple p) L hL

theorem specialImage_three_solvable (hcard : Nat.card K = 3) :
    Group.IsSolvable (specialImage K) := by
  let : Group.IsSolvable
      (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :=
    specialLinearProduct_three_solvable hcard
  exact Group.isSolvable_of_surjective
    (f := specialLinearCover (K := K)) specialLinearCover_surjective

theorem determinant_three_solvable (hcard : Nat.card K = 3) :
    Group.IsSolvable (DeterminantIsometries K) := by
  let : Group.IsSolvable (specialImage K) := specialImage_three_solvable hcard
  exact Group.isSolvable_of_subgroup_quotient (specialImage K)

theorem determinant_three_no_pComponent (hcard : Nat.card K = 3) (p : ℕ)
    (L : Subgroup (DeterminantIsometries K)) : ¬ CFSG.IsPComponent p L := by
  let : Group.IsSolvable (DeterminantIsometries K) := determinant_three_solvable hcard
  exact CatalogueBGeneralLinear.no_pComponent_of_solvable p L

end CFSG.ComponentClassification.CatalogueBOrthogonalFourSplitComponents

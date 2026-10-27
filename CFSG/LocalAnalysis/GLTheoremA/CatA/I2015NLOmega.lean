module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore
import CFSG.SignalizerFunctorTheorem.NonLocal.OrthContract
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.FQ
  CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)

section Plus

variable {K : Type} [Field K] {m : ℕ}

@[expose] noncomputable def omegaPlusEquiv (K : Type) [Field K] (m : ℕ) :
    LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)) ≃*
      matrixProjectiveDerived (coordinateQuadPlus m K) :=
  coordinatePlusWitnessEquiv K (MulEquiv.refl _)

private theorem glFieldAut_reindex_symm_fixed (σ : K ≃+* K) {A : GL (Fin (2 * m)) K}
    (hA : glFieldAut (Fin (2 * m)) K σ A = A) :
    glFieldAut (Fin m ⊕ Fin m) K σ ((reindexMatrixEquiv (plusIndexEquiv m)).symm A) =
      (reindexMatrixEquiv (plusIndexEquiv m)).symm A := by
  apply (reindexMatrixEquiv (plusIndexEquiv m)).injective
  rw [← RecipeFieldOmega.glFieldAut_reindex, MulEquiv.apply_symm_apply, hA]

private theorem omegaPlus_fixed_aux {σ : K ≃+* K}
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hσ : ∀ x : LargeEvenOmega (LargeEvenQPlus K m), f (QuotientGroup.mk x) =
      QuotientGroup.mk (matAct (LargeEvenOmega (LargeEvenQPlus K m))
        (fun σ h hh => omegaPlus_map_mem σ h hh) σ x))
    (A : matrixDerived (reindexQuadraticForm (plusIndexEquiv m) (quadPlus m K)))
    (hA : glFieldAut (Fin (2 * m)) K σ A.val = A.val) :
    f ((statedProjectiveReindexEquiv (plusIndexEquiv m) (quadPlus m K) (coe_quadPlus m K)).symm
        (matrixProjectiveProjection _ A)) =
      (statedProjectiveReindexEquiv (plusIndexEquiv m) (quadPlus m K) (coe_quadPlus m K)).symm
        (matrixProjectiveProjection _ A) := by
  rw [statedProjectiveReindexEquiv_symm_mk]
  set B := (statedDerivedReindexEquiv (plusIndexEquiv m) (quadPlus m K) (coe_quadPlus m K)).symm A
    with hB
  have hfixB : matAct (LargeEvenOmega (LargeEvenQPlus K m))
      (fun σ h hh => omegaPlus_map_mem σ h hh) σ B = B := by
    apply Subtype.ext
    rw [matAct_coe, hB, statedDerivedReindexEquiv_symm_val]
    exact glFieldAut_reindex_symm_fixed σ hA
  exact (hσ B).trans (congrArg QuotientGroup.mk hfixB)

theorem omegaPlus_fixed {σ : K ≃+* K} (k : Subfield K) (hσk : ∀ x, x ∈ k ↔ σ x = x)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hσ : ∀ x : LargeEvenOmega (LargeEvenQPlus K m), f (QuotientGroup.mk x) =
      QuotientGroup.mk (matAct (LargeEvenOmega (LargeEvenQPlus K m))
        (fun σ h hh => omegaPlus_map_mem σ h hh) σ x))
    {t : matrixProjectiveDerived (coordinateQuadPlus m K)}
    (ht : t ∈ subfieldDerivedImage k (coordinateQuadPlus_isExtension k m)) :
    f ((omegaPlusEquiv K m).symm t) = (omegaPlusEquiv K m).symm t := by
  obtain ⟨z, rfl⟩ := ht
  obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective _ z
  rw [incl_mk]
  refine omegaPlus_fixed_aux hσ (inclHom k (coordinateQuadPlus_isExtension k m) y) ?_
  rw [inclHom_val]
  exact glFieldAut_glIncl k hσk _

theorem omegaPlus_nlWitness [Finite K] (hm : 4 ≤ m)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) :
    NLWitness f := by
  obtain ⟨σ, hσ⟩ := matField_spec (LargeEvenOmega (LargeEvenQPlus K m))
    (fun σ h hh => omegaPlus_map_mem σ h hh) hf
  have hσk : ∀ x, x ∈ fixF σ ↔ σ x = x := fun x => mem_fixF
  have hext := coordinateQuadPlus_isExtension (fixF σ) m
  obtain ⟨hnd₀, hT₀⟩ := regular_coordinateQuadPlus m (fixF σ) (by omega)
  obtain ⟨hnd, -⟩ := regular_coordinateQuadPlus m K (by omega)
  have hd : 0 < 2 * m := by omega
  obtain ⟨hs, hna⟩ := matrix_simple_nonabelian hd hnd₀ hT₀
  have hsJ : IsSimpleGroup ↥(subfieldDerivedImage (fixF σ) hext) := by
    haveI := hs
    exact (inclEquiv (fixF σ) hext hd).symm.isSimpleGroup
  have hnaJ : ∃ x y : ↥(subfieldDerivedImage (fixF σ) hext), x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hna
    refine ⟨inclEquiv (fixF σ) hext hd a, inclEquiv (fixF σ) hext hd b, fun h => hab
      ((inclEquiv (fixF σ) hext hd).injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hNL := CFSG.SignalizerFunctorTheorem.NonLocal.Orth.nonLocalized_orthogonalSubfield (fixF σ)
    hext hnd₀ hnd hT₀ (by omega)
    (CFSG.SignalizerFunctorTheorem.NonLocal.le_pow_sub_four _ Finite.one_lt_card (2 * m) (by omega))
  refine nlWitness_of_nonLocalized (omegaPlusEquiv K m) hsJ hnaJ hNL ?_
  rintro _ ⟨t, ht, rfl⟩
  exact omegaPlus_fixed (fixF σ) hσk hσ ht

end Plus

section Family

set_option linter.unusedSectionVars false


theorem i2015NLOnOmegaPlus_holds : I2015NLOnOmegaPlus := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_
    (fun p _ h => by rw [ht] at h; exact absurd h.1 (by decide))
  intro p _ _ _ _ hC
  obtain ⟨t, r, n⟩ := lab
  dsimp only [regRankGe] at hC ht
  subst ht
  intro Q hQ
  have hr3 : r ≠ 3 := by omega
  simp only [CFSG.Assembly.LargeEvenRawDatum, hr3, if_false] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  exact ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf _ _ _ => omegaPlus_nlWitness (by omega) hf⟩

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end

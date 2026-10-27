module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open Matrix CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_tail_model_point_family_invariant)

theorem reindexMatrixEquiv_glFieldEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {d : ℕ} (e : ι ≃ Fin d) (φ : F ≃+* F) (A : GL ι F) :
    reindexMatrixEquiv e (glFieldEquiv ι φ A) = glFieldEquiv (Fin d) φ (reindexMatrixEquiv e A) :=
  rfl

section Glue

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] {d : ℕ}

theorem exists_similarity_of_mem_image (eI : ι ≃ Fin d) (Q : QuadraticForm F (ι → F))
    {Q₀ : (ι → F) → F} (hQ : ⇑Q = Q₀) (β : MulAut (StatedProj (StatedOmega Q₀)))
    (hβ : MulAut.congr (statedProjectiveReindexEquiv eI Q hQ) β ∈
      matrixProjectiveImage (reindexQuadraticForm eI Q)) :
    ∃ (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v : ι → F, Q (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) ∧
      ∀ x : StatedOmega Q₀, ∃ y : StatedOmega Q₀,
        (y : GL ι F) = A * glFieldEquiv ι φ (x : GL ι F) * A⁻¹ ∧
          β (QuotientGroup.mk x) = QuotientGroup.mk y := by
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ _).mp hβ
  set e := statedProjectiveReindexEquiv eI Q hQ with he
  refine ⟨(reindexMatrixEquiv eI).symm g.val.left, g.val.right, multiplier _ g, fun v => ?_,
    fun x => ?_⟩
  · have h1 := multiplier_spec (reindexQuadraticForm eI Q) g (reindexVectorEquiv eI v)
    have h2 : coordinateSemilinearMap g.val (reindexVectorEquiv eI v) =
        reindexVectorEquiv eI (((reindexMatrixEquiv eI).symm g.val.left).val *ᵥ
          (fun i => g.val.right (v i))) := by
      rw [← reindexMatrixEquiv_mulVec eI ((reindexMatrixEquiv eI).symm g.val.left)
        (fun i => g.val.right (v i)), MulEquiv.apply_symm_apply, matrixLinearEquiv_apply]
      rfl
    rw [h2, reindexQuadraticForm_map, reindexQuadraticForm_map] at h1
    exact h1
  · set xc := statedDerivedReindexEquiv eI Q hQ x with hxc
    set yc := matrixDerivedConjugation (reindexQuadraticForm eI Q) g xc with hyc
    refine ⟨(statedDerivedReindexEquiv eI Q hQ).symm yc, ?_, ?_⟩
    · have key : (reindexMatrixEquiv eI).symm
          (glFieldAut (Fin d) F g.val.right ((reindexMatrixEquiv eI) (x : GL ι F))) =
          glFieldEquiv ι g.val.right (x : GL ι F) := by
        have h : (glFieldAut (Fin d) F g.val.right) ((reindexMatrixEquiv eI) (x : GL ι F)) =
            (reindexMatrixEquiv eI) (glFieldEquiv ι g.val.right (x : GL ι F)) := rfl
        rw [h]
        exact (reindexMatrixEquiv eI).symm_apply_apply _
      rw [statedDerivedReindexEquiv_symm_val, hyc, matrixDerivedConjugation_val, hxc,
        statedDerivedReindexEquiv_val, map_mul, map_mul, key, map_inv]
    · have h3 : e (QuotientGroup.mk x) =
          matrixProjectiveProjection (reindexQuadraticForm eI Q) xc :=
        statedProjectiveReindexEquiv_mk eI Q hQ x
      have h5 : e (QuotientGroup.mk ((statedDerivedReindexEquiv eI Q hQ).symm yc)) =
          matrixProjectiveProjection (reindexQuadraticForm eI Q) yc := by
        have := statedProjectiveReindexEquiv_mk eI Q hQ
          ((statedDerivedReindexEquiv eI Q hQ).symm yc)
        rw [MulEquiv.apply_symm_apply] at this
        exact this
      apply e.injective
      rw [h5]
      have h6 : e (β (QuotientGroup.mk x)) = (MulAut.congr e β) (e (QuotientGroup.mk x)) := by
        simp [MulAut.congr_apply]
      rw [h6, ← hg, h3, hyc, matrixProjectiveConjugation_mk]

end Glue


section AllAut

variable {p f : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_similarity_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p f)
    (hF : Nat.card F = p ^ f) (β : MulAut (StatedProj (StatedOmega (StatedQuadOdd n F)))) :
    ∃ (A : GL (Fin n ⊕ Fin n ⊕ Unit) F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v, quadOdd n F (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadOdd n F v)) ∧
      ∀ x : StatedOmega (StatedQuadOdd n F), ∃ y : StatedOmega (StatedQuadOdd n F),
        (y : GL (Fin n ⊕ Fin n ⊕ Unit) F) = A * glFieldEquiv _ φ (x : GL _ F) * A⁻¹ ∧
          β (QuotientGroup.mk x) = QuotientGroup.mk y := by
  have h : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n F))) .POmegaOdd n p f :=
    ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  refine exists_similarity_of_mem_image (oddIndexEquiv n) (quadOdd n F) (coe_quadOdd n F) β ?_
  exact mem_image_of_familyAut_eq_top
    (orthogonal_geometry_tail_model_point_family_invariant _ .POmegaOdd (.inl rfl) n p f h F hF).2
    (coordinate_odd_family_eq_matrixImage h F hF (MulEquiv.refl _)) _

theorem exists_similarity_plus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (hn : 5 ≤ n) (hF : Nat.card F = p ^ f)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus n F)))) :
    ∃ (A : GL (Fin n ⊕ Fin n) F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v, quadPlus n F (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadPlus n F v)) ∧
      ∀ x : StatedOmega (StatedQuadPlus n F), ∃ y : StatedOmega (StatedQuadPlus n F),
        (y : GL (Fin n ⊕ Fin n) F) = A * glFieldEquiv _ φ (x : GL _ F) * A⁻¹ ∧
          β (QuotientGroup.mk x) = QuotientGroup.mk y := by
  have h : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n F))) .POmegaPlus n p f :=
    ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  refine exists_similarity_of_mem_image (plusIndexEquiv n) (quadPlus n F) (coe_quadPlus n F) β ?_
  exact mem_image_of_familyAut_eq_top
    (CatalogueBOrthogonalPointPlusFamilyOrbit.coordinate_plus_pointFamilyAut_eq_top hn)
    (coordinate_plus_family_eq_matrixImage h F hF (MulEquiv.refl _)) _

theorem exists_similarity_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p f)
    (hF : Nat.card F = p ^ f) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadMinus n F b c)))) :
    ∃ (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v, quadMinus n F b c (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadMinus n F b c v)) ∧
      ∀ x : StatedOmega (StatedQuadMinus n F b c), ∃ y : StatedOmega (StatedQuadMinus n F b c),
        (y : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) =
          A * glFieldEquiv _ φ (x : GL _ F) * A⁻¹ ∧
          β (QuotientGroup.mk x) = QuotientGroup.mk y := by
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  have h : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n F b c))) .POmegaMinus
      n p f := ⟨hadm, F, inferInstance, inferInstance, hF, b, c, hirr, ⟨MulEquiv.refl _⟩⟩
  refine exists_similarity_of_mem_image (minusIndexEquiv n hn) (quadMinus n F b c)
    (coe_quadMinus n F b c) β ?_
  exact mem_image_of_familyAut_eq_top
    (orthogonal_geometry_tail_model_point_family_invariant _ .POmegaMinus (.inr rfl) n p f h hn
      F hF b c hirr).2
    (coordinate_minus_family_eq_matrixImage h hn F hF b c hirr (MulEquiv.refl _)) _

end AllAut

end CFSG.ClassicalInvolution.ModelFacts.OrthAut

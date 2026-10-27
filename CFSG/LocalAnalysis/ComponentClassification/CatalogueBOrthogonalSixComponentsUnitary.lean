module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixActionSimilitudes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometrySpaces
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix CatalogueBOrthogonalFourNonsplit CatalogueBUnitaryIsometry
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

universe u

variable {K : Type u} [Field K] (delta : K) [Fact (¬ IsSquare delta)]

@[expose] def sixHermitianForm :
    (Fin 4 → extension delta) →ₛₗ[(conjugation delta).toRingEquiv.toRingHom]
      (Fin 4 → extension delta) →ₗ[extension delta] extension delta :=
  CatalogueBHermitian.matrixForm (conjugation delta).toRingEquiv (sixGram (extension delta))

theorem sixHermitianForm_isSymm : (sixHermitianForm delta).IsSymm := by
  apply CatalogueBHermitian.matrixForm_isSymm _ (conjugation_square delta)
  change (sixBar delta (sixGram (extension delta))).transpose = sixGram (extension delta)
  rw [sixBar_gram, sixGram_transpose]

theorem sixHermitianForm_nondegenerate : (sixHermitianForm delta).Nondegenerate :=
  CatalogueBHermitian.matrixForm_nondegenerate (conjugation delta).toRingEquiv
    (sixGramGL (extension delta))

theorem six_conjTr_eq (A : Matrix (Fin 4) (Fin 4) (extension delta)) :
    conjTr (conjugation delta).toRingEquiv A = (sixBar delta A).transpose := by
  apply Matrix.ext
  intro i j
  rfl

theorem six_hermitian_isometry_iff_matrix (A : Matrix (Fin 4) (Fin 4) (extension delta)) :
    (∀ x y, sixHermitianForm delta (A *ᵥ x) (A *ᵥ y) = sixHermitianForm delta x y) ↔
      (sixBar delta A).transpose * sixGram (extension delta) * A =
        sixGram (extension delta) := by
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    have hij := h (Pi.single i 1) (Pi.single j 1)
    change CatalogueBHermitian.matrixForm (conjugation delta).toRingEquiv _
      (A *ᵥ Pi.single i 1) (A *ᵥ Pi.single j 1) =
      CatalogueBHermitian.matrixForm (conjugation delta).toRingEquiv _
        (Pi.single i 1) (Pi.single j 1) at hij
    rw [CatalogueBHermitian.matrixForm_mulVec, CatalogueBHermitian.matrixForm_apply,
      herm_single_left, herm_single_left, map_one, one_mul, mulVec_single_one,
      mulVec_single_one] at hij
    rw [six_conjTr_eq] at hij
    simpa only [Matrix.col_apply, one_mul] using hij
  · intro h x y
    change CatalogueBHermitian.matrixForm (conjugation delta).toRingEquiv _
      (A *ᵥ x) (A *ᵥ y) = _
    rw [CatalogueBHermitian.matrixForm_mulVec]
    change herm _ x (((sixBar delta A).transpose * sixGram (extension delta) * A) *ᵥ y) = _
    rw [h]
    rfl

@[expose] def sixSpecialLinearMatrix (A : sixSpecialUnitary delta) :
    SpecialLinearGroup (Fin 4) (extension delta) := ⟨A.val.val, A.property.2⟩

@[expose] def sixSpecialIsometryMatrix (g : specialIsometry (sixHermitianForm delta)) :
    SpecialLinearGroup (Fin 4) (extension delta) :=
  ⟨LinearMap.toMatrix' g.val.val.toLinearMap, by
    rw [LinearMap.det_toMatrix']
    exact (mem_specialIsometry_iff _ g.val).mp g.property⟩

@[expose] def sixSpecialUnitarySpaceEquiv :
    sixSpecialUnitary delta ≃* specialIsometry (sixHermitianForm delta) where
  toFun A := ⟨⟨SpecialLinearGroup.toLin' (sixSpecialLinearMatrix delta A), by
    intro x y
    change sixHermitianForm delta (A.val.val *ᵥ x) (A.val.val *ᵥ y) = _
    exact (six_hermitian_isometry_iff_matrix delta A.val.val).mpr A.property.1 x y⟩, by
    rw [mem_specialIsometry_iff]
    change LinearMap.det (Matrix.toLin' A.val.val) = 1
    rw [← LinearMap.det_toMatrix', LinearMap.toMatrix'_toLin']
    exact A.property.2⟩
  invFun g := ⟨SpecialLinearGroup.toGL (sixSpecialIsometryMatrix delta g), by
    constructor
    · apply (six_hermitian_isometry_iff_matrix delta _).mp
      intro x y
      change sixHermitianForm delta ((LinearMap.toMatrix' g.val.val.toLinearMap) *ᵥ x)
        ((LinearMap.toMatrix' g.val.val.toLinearMap) *ᵥ y) = _
      rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
      exact g.val.property x y
    · exact (sixSpecialIsometryMatrix delta g).property⟩
  left_inv A := by
    apply Subtype.ext
    apply Units.ext
    exact LinearMap.toMatrix'_toLin' A.val.val
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact Matrix.toLin'_toMatrix' g.val.val.toLinearMap
  map_mul' A B := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact Matrix.toLin'_mul A.val.val B.val.val

theorem sixSpecialUnitarySpaceEquiv_apply (A : sixSpecialUnitary delta)
    (x : Fin 4 → extension delta) :
    (sixSpecialUnitarySpaceEquiv delta A).val.val x = A.val.val *ᵥ x := rfl

theorem sixSpecialUnitarySpaceEquiv_symm_val (g : specialIsometry (sixHermitianForm delta)) :
    ((sixSpecialUnitarySpaceEquiv delta).symm g).val.val =
      LinearMap.toMatrix' g.val.val.toLinearMap := rfl

variable [Finite K]

theorem exists_six_special_unitary_equiv (h2 : (2 : K) ≠ 0) :
    Nonempty (sixSpecialUnitary delta ≃* SUid (conjugation delta).toRingEquiv 4) := by
  let : Finite (extension delta) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd delta 0).symm
  obtain ⟨_, _, _, ⟨e⟩⟩ := exists_native_isometry_groups (sixHermitianForm delta)
    (sixHermitianForm_isSymm delta) (sixHermitianForm_nondegenerate delta)
    (conjugation_square delta) (conjugation_ne_one delta h2)
  have hd : Module.finrank (extension delta) (Fin 4 → extension delta) = 4 :=
    Module.finrank_fin_fun _
  rw [hd] at e
  exact ⟨(sixSpecialUnitarySpaceEquiv delta).trans e⟩

theorem sixSpecialUnitary_quasisimple (h2 : (2 : K) ≠ 0) :
    CFSG.IsQuasisimple (sixSpecialUnitary delta) := by
  let : Finite (extension delta) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd delta 0).symm
  obtain ⟨e⟩ := exists_six_special_unitary_equiv delta h2
  have hG := SUid_quasisimple_finite (conjugation delta).toRingEquiv
    (conjugation_square delta) (conjugation_ne_one delta h2) 4 (by decide)
    (by intro h; have hh := congrArg Prod.fst h; norm_num at hh)
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv e (CatalogueBAlternating.quasisimple_iff_native.mp hG))

end CFSG.ComponentClassification.CatalogueBOrthogonalSix

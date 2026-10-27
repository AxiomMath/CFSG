module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open Matrix CatalogueBHigherLinearField

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem coordinateSemilinearMap_inl (A : GL (Fin d) K) (v : Fin d → K) :
    coordinateSemilinearMap (SemidirectProduct.inl A) v = matrixLinearEquiv A v := rfl

@[expose] def matrixIsometryInclusion (Q : QuadraticForm K (Fin d → K)) :
    matrixIsometries Q →* similarityPairs Q where
  toFun A := ⟨SemidirectProduct.inl A.val, by
    refine ⟨1, fun v => ?_⟩
    rw [coordinateSemilinearMap_inl]
    change Q (matrixLinearEquiv A.val v) = (1 : K) * Q v
    rw [one_mul]
    exact (mem_matrixIsometries_iff Q A.val).mp A.property v⟩
  map_one' := Subtype.ext (map_one SemidirectProduct.inl)
  map_mul' A B := Subtype.ext (map_mul SemidirectProduct.inl A.val B.val)

theorem matrixIsometryInclusion_val (Q : QuadraticForm K (Fin d → K))
    (A : matrixIsometries Q) :
    (matrixIsometryInclusion Q A).val = SemidirectProduct.inl A.val := rfl

theorem matrixIsometryInclusion_injective (Q : QuadraticForm K (Fin d → K)) :
    Function.Injective (matrixIsometryInclusion Q) := by
  intro A B h
  apply Subtype.ext
  exact SemidirectProduct.inl_injective (φ := glFieldAut (Fin d) K)
    (congrArg Subtype.val h)

@[expose] def matrixIsometryPairs (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (similarityPairs Q) := (matrixIsometryInclusion Q).range

theorem mem_matrixIsometryPairs_iff (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    g ∈ matrixIsometryPairs Q ↔ g.val.left ∈ matrixIsometries Q ∧ g.val.right = 1 := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.property, rfl⟩
  · rintro ⟨hA, hfield⟩
    refine ⟨⟨g.val.left, hA⟩, ?_⟩
    apply Subtype.ext
    exact SemidirectProduct.ext rfl hfield.symm

@[expose] def matrixDerivedInclusion (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q →* similarityPairs Q :=
  (matrixIsometryInclusion Q).comp (Subgroup.inclusion (matrixDerived_le_isometries Q))

theorem matrixDerivedInclusion_val (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    (matrixDerivedInclusion Q A).val = SemidirectProduct.inl A.val := rfl

theorem matrixDerivedInclusion_injective (Q : QuadraticForm K (Fin d → K)) :
    Function.Injective (matrixDerivedInclusion Q) := by
  intro A B h
  apply Subtype.ext
  exact SemidirectProduct.inl_injective (φ := glFieldAut (Fin d) K)
    (congrArg Subtype.val h)

@[expose] def matrixDerivedPairs (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (similarityPairs Q) := (matrixDerivedInclusion Q).range

theorem mem_matrixDerivedPairs_iff (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    g ∈ matrixDerivedPairs Q ↔ g.val.left ∈ matrixDerived Q ∧ g.val.right = 1 := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.property, rfl⟩
  · rintro ⟨hA, hfield⟩
    refine ⟨⟨g.val.left, hA⟩, ?_⟩
    apply Subtype.ext
    exact SemidirectProduct.ext rfl hfield.symm

theorem matrixDerivedPairs_le_isometryPairs (Q : QuadraticForm K (Fin d → K)) :
    matrixDerivedPairs Q ≤ matrixIsometryPairs Q := by
  intro g hg
  rw [mem_matrixDerivedPairs_iff] at hg
  exact (mem_matrixIsometryPairs_iff Q g).mpr
    ⟨matrixDerived_le_isometries Q hg.1, hg.2⟩

theorem matrixIsometryPairs_map (Q : QuadraticForm K (Fin d → K)) :
    (matrixIsometryPairs Q).map (similarityPairs Q).subtype =
      (matrixIsometries Q).map SemidirectProduct.inl := by
  rw [matrixIsometryPairs, ← MonoidHom.range_comp]
  change (SemidirectProduct.inl.comp (matrixIsometries Q).subtype).range = _
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem matrixDerivedPairs_map (Q : QuadraticForm K (Fin d → K)) :
    (matrixDerivedPairs Q).map (similarityPairs Q).subtype =
      (matrixDerived Q).map SemidirectProduct.inl := by
  rw [matrixDerivedPairs, ← MonoidHom.range_comp]
  change (SemidirectProduct.inl.comp (matrixDerived Q).subtype).range = _
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem matrixDerivedPairs_eq_commutator (Q : QuadraticForm K (Fin d → K)) :
    matrixDerivedPairs Q = ⁅matrixIsometryPairs Q, matrixIsometryPairs Q⁆ := by
  apply Subgroup.map_injective (similarityPairs Q).subtype_injective
  rw [matrixDerivedPairs_map, Subgroup.map_commutator, matrixIsometryPairs_map,
    ← Subgroup.map_commutator]
  rfl

theorem matrixDerivedInclusion_conjugation (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (A : matrixDerived Q) :
    matrixDerivedInclusion Q (matrixDerivedConjugation Q g A) =
      g * matrixDerivedInclusion Q A * g⁻¹ := by
  apply Subtype.ext
  exact matrixConjugation_inl g.val A.val

instance matrixIsometryPairs_normal (Q : QuadraticForm K (Fin d → K)) :
    (matrixIsometryPairs Q).Normal where
  conj_mem n hn g := by
    obtain ⟨A, rfl⟩ := hn
    refine ⟨⟨matrixConjugation g.val A.val,
      matrixConjugation_mem_isometries Q g A.val A.property⟩, ?_⟩
    apply Subtype.ext
    exact matrixConjugation_inl g.val A.val

instance matrixDerivedPairs_normal (Q : QuadraticForm K (Fin d → K)) :
    (matrixDerivedPairs Q).Normal where
  conj_mem n hn g := by
    obtain ⟨A, rfl⟩ := hn
    exact ⟨matrixDerivedConjugation Q g A, matrixDerivedInclusion_conjugation Q g A⟩

theorem matrixIsometryPairs_le_linearPairs (Q : QuadraticForm K (Fin d → K)) :
    matrixIsometryPairs Q ≤ linearSimilarityPairs Q := by
  intro g hg
  exact (mem_linearSimilarityPairs_iff Q g).mpr
    ((mem_matrixIsometryPairs_iff Q g).mp hg).2

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

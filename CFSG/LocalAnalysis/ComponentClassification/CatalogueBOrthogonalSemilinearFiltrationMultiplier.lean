module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataEmbedding

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration

open CatalogueBOrthogonalSemilinear

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem exists_nonzero_value (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0) :
    ∃ v, Q v ≠ 0 := by
  by_contra h
  push Not at h
  apply hQ
  ext v
  exact h v

instance linearPairsNormal (Q : QuadraticForm K (Fin d → K)) :
    (linearSimilarityPairs Q).Normal := by
  change (fieldProjection Q).ker.Normal
  infer_instance

instance isometryLinearNormal (Q : QuadraticForm K (Fin d → K)) :
    ((matrixIsometryPairs Q).subgroupOf (linearSimilarityPairs Q)).Normal :=
  inferInstance

theorem fieldProjection_kernel (Q : QuadraticForm K (Fin d → K)) :
    (fieldProjection Q).ker = linearSimilarityPairs Q := rfl

theorem linear_fieldProjection (Q : QuadraticForm K (Fin d → K))
    (g : linearSimilarityPairs Q) : fieldProjection Q g.val = 1 := g.property

theorem linear_pair_val (Q : QuadraticForm K (Fin d → K))
    (g : linearSimilarityPairs Q) :
    g.val.val = SemidirectProduct.inl g.val.val.left :=
  SemidirectProduct.ext rfl
    ((mem_linearSimilarityPairs_iff Q g.val).mp g.property)

@[expose] def multiplierHom (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) : linearSimilarityPairs Q →* Kˣ where
  toFun g := multiplier Q g.val
  map_one' := multiplier_one Q hQ
  map_mul' g h := by
    change multiplier Q (g.val * h.val) = multiplier Q g.val * multiplier Q h.val
    rw [multiplier_mul Q hQ, (mem_linearSimilarityPairs_iff Q g.val).mp g.property]
    rfl

theorem multiplierHom_apply (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (g : linearSimilarityPairs Q) :
    multiplierHom Q hQ g = multiplier Q g.val := rfl

theorem multiplierHom_spec (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (g : linearSimilarityPairs Q) (v : Fin d → K) :
    Q (matrixLinearEquiv g.val.val.left v) = (multiplierHom Q hQ g : K) * Q v := by
  have h := multiplier_spec Q g.val v
  rw [linear_pair_val Q g, coordinateSemilinearMap_inl] at h
  exact h

theorem multiplierHom_eq_one_iff (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (g : linearSimilarityPairs Q) :
    multiplierHom Q hQ g = 1 ↔ g.val ∈ matrixIsometryPairs Q := by
  rw [mem_matrixIsometryPairs_iff]
  constructor
  · intro hg
    refine ⟨?_, (mem_linearSimilarityPairs_iff Q g.val).mp g.property⟩
    apply (mem_matrixIsometries_iff Q g.val.val.left).mpr
    intro v
    have h := multiplierHom_spec Q hQ g v
    rw [hg] at h
    simpa using h
  · rintro ⟨hA, _⟩
    apply multiplier_unique Q hQ g.val.val _ _ (multiplier_spec Q g.val)
    intro v
    rw [linear_pair_val Q g, coordinateSemilinearMap_inl]
    change Q (matrixLinearEquiv g.val.val.left v) = (1 : K) * Q v
    rw [one_mul]
    exact (mem_matrixIsometries_iff Q g.val.val.left).mp hA v

theorem multiplierHom_kernel (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) :
    (multiplierHom Q hQ).ker =
      (matrixIsometryPairs Q).subgroupOf (linearSimilarityPairs Q) := by
  ext g
  exact multiplierHom_eq_one_iff Q hQ g

theorem fieldProjection_isometry (Q : QuadraticForm K (Fin d → K))
    (A : matrixIsometries Q) : fieldProjection Q (matrixIsometryInclusion Q A) = 1 := rfl

theorem multiplierHom_isometry (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (A : matrixIsometries Q) :
    multiplierHom Q hQ
      ⟨matrixIsometryInclusion Q A, fieldProjection_isometry Q A⟩ = 1 :=
  (multiplierHom_eq_one_iff Q hQ _).mpr ⟨A, rfl⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration

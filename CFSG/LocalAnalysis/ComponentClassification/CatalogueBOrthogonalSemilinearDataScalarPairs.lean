module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataEmbedding

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open Matrix

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def matrixScalarPairs (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (similarityPairs Q) :=
  (matrixDerivedScalars Q).map (matrixDerivedInclusion Q)

theorem matrixScalarPairs_le_derivedPairs (Q : QuadraticForm K (Fin d → K)) :
    matrixScalarPairs Q ≤ matrixDerivedPairs Q := by
  rintro g ⟨A, _, rfl⟩
  exact ⟨A, rfl⟩

theorem mem_matrixScalarPairs_iff (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    g ∈ matrixScalarPairs Q ↔ g.val.left ∈ matrixDerived Q ∧ g.val.right = 1 ∧
      ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin d) c = g.val.left := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A.property, rfl, (mem_matrixDerivedScalars_iff Q A).mp hA⟩
  · rintro ⟨hA, hfield, c, hc⟩
    refine ⟨⟨g.val.left, hA⟩,
      (mem_matrixDerivedScalars_iff Q ⟨g.val.left, hA⟩).mpr ⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    exact SemidirectProduct.ext rfl hfield.symm

instance matrixScalarPairs_normal (Q : QuadraticForm K (Fin d → K)) :
    (matrixScalarPairs Q).Normal where
  conj_mem n hn g := by
    obtain ⟨A, hA, rfl⟩ := hn
    refine ⟨matrixDerivedConjugation Q g A, ?_, matrixDerivedInclusion_conjugation Q g A⟩
    rw [← matrixDerivedScalars_invariant Q g]
    exact Subgroup.mem_map_of_mem (matrixDerivedConjugation Q g).toMonoidHom hA

@[expose] def matrixDerivedPairEquiv (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q ≃* matrixDerivedPairs Q :=
  MonoidHom.ofInjective (matrixDerivedInclusion_injective Q)

theorem matrixDerivedPairEquiv_val (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    (matrixDerivedPairEquiv Q A).val = matrixDerivedInclusion Q A := rfl

theorem matrixDerivedPairEquiv_conjugation (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (A : matrixDerived Q) :
    matrixDerivedPairEquiv Q (matrixDerivedConjugation Q g A) =
      MulAut.conjNormal g (matrixDerivedPairEquiv Q A) := by
  apply Subtype.ext
  exact matrixDerivedInclusion_conjugation Q g A

@[expose] def matrixPairScalars (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (matrixDerivedPairs Q) :=
  (matrixScalarPairs Q).subgroupOf (matrixDerivedPairs Q)

instance matrixPairScalars_normal (Q : QuadraticForm K (Fin d → K)) :
    (matrixPairScalars Q).Normal := by
  unfold matrixPairScalars
  infer_instance

theorem matrixDerivedScalars_map_pairEquiv (Q : QuadraticForm K (Fin d → K)) :
    (matrixDerivedScalars Q).map (matrixDerivedPairEquiv Q).toMonoidHom =
      matrixPairScalars Q := by
  ext g
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, rfl⟩
  · rintro ⟨A, hA, hAg⟩
    exact ⟨A, hA, Subtype.ext hAg⟩

abbrev matrixPairProjectiveDerived (Q : QuadraticForm K (Fin d → K)) :=
  matrixDerivedPairs Q ⧸ matrixPairScalars Q

@[expose] def matrixProjectivePairEquiv (Q : QuadraticForm K (Fin d → K)) :
    matrixProjectiveDerived Q ≃* matrixPairProjectiveDerived Q :=
  QuotientGroup.congr (matrixDerivedScalars Q) (matrixPairScalars Q)
    (matrixDerivedPairEquiv Q) (matrixDerivedScalars_map_pairEquiv Q)

theorem matrixProjectivePairEquiv_mk (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    matrixProjectivePairEquiv Q (matrixProjectiveProjection Q A) =
      QuotientGroup.mk' (matrixPairScalars Q) (matrixDerivedPairEquiv Q A) :=
  QuotientGroup.congr_mk' _ _ _ _ A

@[expose] def matrixPairProjectiveProjection (Q : QuadraticForm K (Fin d → K)) :
    matrixDerivedPairs Q →* matrixPairProjectiveDerived Q := QuotientGroup.mk' _

theorem matrixPairProjectiveProjection_surjective (Q : QuadraticForm K (Fin d → K)) :
    Function.Surjective (matrixPairProjectiveProjection Q) := QuotientGroup.mk'_surjective _

theorem matrixPairProjectiveProjection_kernel (Q : QuadraticForm K (Fin d → K)) :
    (matrixPairProjectiveProjection Q).ker = matrixPairScalars Q := QuotientGroup.ker_mk' _

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

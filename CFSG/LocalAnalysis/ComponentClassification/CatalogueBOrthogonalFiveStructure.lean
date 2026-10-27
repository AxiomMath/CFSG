module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

theorem selfAdjoint_isometry_exhaustion (h2 : (2 : K) ≠ 0)
    (g : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) :
    ∃ A : symplecticSimilitudes K, g = selfAdjointOrthogonalAction h2 A ∨
      g = selfAdjointOrthogonalAction h2 A *
        QuadraticMap.negOrthogonal (selfAdjointForm K) := by
  obtain ⟨⟨A, ε⟩, rfl⟩ := selfAdjointFullAction_surjective h2 g
  refine ⟨A, ?_⟩
  have hs : ε.val = 1 ∨ ε.val = -1 :=
    Units.eq_or_eq_neg_of_sq_eq_sq ε.val 1
      (by
        apply Units.ext
        rw [pow_two, one_pow]
        change (ε.val : K) * (ε.val : K) = 1
        simpa only [pow_two] using (mem_rootsOfUnity' 2 ε.val).mp ε.property)
  rcases hs with hε | hε
  · have he : ε = 1 := Subtype.ext hε
    apply Or.inl
    change selfAdjointOrthogonalAction h2 A * selfAdjointScalarAction ε = _
    rw [he, map_one, mul_one]
  · have he : ε = selfAdjointNegSign K := Subtype.ext hε
    apply Or.inr
    change selfAdjointOrthogonalAction h2 A * selfAdjointScalarAction ε = _
    rw [he, selfAdjointScalarAction_neg]

theorem selfAdjoint_isometry_generation (h2 : (2 : K) ≠ 0) :
    Subgroup.closure
      ((Set.range (selfAdjointOrthogonalAction h2) :
        Set (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K))) ∪
        {QuadraticMap.negOrthogonal (selfAdjointForm K)}) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨A, rfl | rfl⟩ := selfAdjoint_isometry_exhaustion h2 g
  · exact Subgroup.subset_closure (Or.inl ⟨A, rfl⟩)
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨A, rfl⟩))
      (Subgroup.subset_closure (Or.inr rfl))

theorem selfAdjoint_five_full_isometry_structure (h2 : (2 : K) ≠ 0) :
    Module.finrank K (selfAdjointSubmodule K) = 5 ∧
    (selfAdjointForm K).polarBilin.Nondegenerate ∧
    (∀ X : selfAdjointSubmodule K,
      X.val * X.val = selfAdjointForm K X • (1 : Matrix (Fin 4) (Fin 4) K)) ∧
    (∀ A : (symplecticMultiplier (K := K)).ker,
      selfAdjointSymplecticAction h2 A = 1 ↔
        A.val.val.val = (1 : Matrix (Fin 4) (Fin 4) K) ∨
          A.val.val.val = -(1 : Matrix (Fin 4) (Fin 4) K)) ∧
    (selfAdjointSymplecticAction h2).ker ≤
      Subgroup.center (symplecticMultiplier (K := K)).ker ∧
    (∀ g : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K),
      ∃ A : symplecticSimilitudes K, g = selfAdjointOrthogonalAction h2 A ∨
        g = selfAdjointOrthogonalAction h2 A *
          QuadraticMap.negOrthogonal (selfAdjointForm K)) ∧
    (selfAdjointSymplecticImage h2).Normal ∧
    IsMulCommutative
      (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) ⧸
        selfAdjointSymplecticImage h2) :=
  ⟨selfAdjoint_finrank h2, selfAdjointForm_nondegenerate h2, selfAdjoint_square h2,
    selfAdjointSymplecticAction_kernel_sign h2, selfAdjointSymplecticAction_kernel_le_center h2,
    selfAdjoint_isometry_exhaustion h2, inferInstance, inferInstance⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalFive

module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveReflection
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

@[expose] def selfAdjointScalarAction :
    rootsOfUnity 2 K →* TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) where
  toFun ε := ⟨LinearEquiv.smulOfUnit ε.val,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (by
      intro X
      change selfAdjointForm K ((ε.val : K) • X) = selfAdjointForm K X
      rw [QuadraticMap.map_smul, smul_eq_mul]
      have hε : (ε.val : K) * (ε.val : K) = 1 := by
        simpa only [pow_two] using (mem_rootsOfUnity' 2 ε.val).mp ε.property
      rw [hε, one_mul])⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    change (1 : K) • X = X
    exact one_smul K X
  map_mul' ε δ := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    change ((ε.val : K) * (δ.val : K)) • X = (ε.val : K) • ((δ.val : K) • X)
    exact mul_smul _ _ _

theorem selfAdjointScalarAction_val (ε : rootsOfUnity 2 K) (X : selfAdjointSubmodule K) :
    ((selfAdjointScalarAction ε).val X).val = (ε.val : K) • X.val := rfl

@[expose] def selfAdjointNegSign (K : Type u) [Field K] : rootsOfUnity 2 K :=
  ⟨(-1 : Kˣ), by simp [mem_rootsOfUnity, pow_two]⟩

theorem selfAdjointScalarAction_neg :
    selfAdjointScalarAction (selfAdjointNegSign K) =
      QuadraticMap.negOrthogonal (selfAdjointForm K) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  rw [QuadraticMap.coe_negOrthogonal]
  change (-1 : K) • X = -X
  exact neg_one_smul K X

theorem selfAdjointScalarAction_commute (h2 : (2 : K) ≠ 0)
    (ε : rootsOfUnity 2 K) (A : symplecticSimilitudes K) :
    Commute (selfAdjointScalarAction ε) (selfAdjointOrthogonalAction h2 A) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change (ε.val : K) • selfAdjointConjugation A X =
    selfAdjointConjugation A ((ε.val : K) • X)
  exact (selfAdjointConjugation A).map_smul _ _ |>.symm

@[expose] def selfAdjointFullAction (h2 : (2 : K) ≠ 0) :
    symplecticSimilitudes K × rootsOfUnity 2 K →*
      TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) where
  toFun x := selfAdjointOrthogonalAction h2 x.1 * selfAdjointScalarAction x.2
  map_one' := by simp
  map_mul' x y := by
    change selfAdjointOrthogonalAction h2 (x.1 * y.1) *
      selfAdjointScalarAction (x.2 * y.2) = _
    rw [map_mul, map_mul]
    exact ((selfAdjointScalarAction_commute h2 x.2 y.1).mul_mul_mul_comm _ _).symm

theorem selfAdjointFullAction_val (h2 : (2 : K) ≠ 0)
    (x : symplecticSimilitudes K × rootsOfUnity 2 K) (X : selfAdjointSubmodule K) :
    ((selfAdjointFullAction h2 x).val X).val =
      (x.2.val : K) • (x.1.val.val * X.val * x.1.val⁻¹.val) := by
  change (selfAdjointConjugation x.1 ((x.2.val : K) • X)).val = _
  rw [map_smul]
  rfl

theorem selfAdjoint_reflection_mem_fullAction (h2 : (2 : K) ≠ 0)
    (X : selfAdjointSubmodule K) [Invertible (selfAdjointForm K X)] :
    TauCeti.QuadraticMap.reflectionOrthogonal (selfAdjointForm K) X ∈
      (selfAdjointFullAction h2).range := by
  refine ⟨(selfAdjointAnisotropicSimilitude h2 X (isUnit_of_invertible _).ne_zero,
    selfAdjointNegSign K), ?_⟩
  change selfAdjointOrthogonalAction h2 _ * selfAdjointScalarAction (selfAdjointNegSign K) = _
  rw [← (selfAdjointScalarAction_commute h2 (selfAdjointNegSign K) _).eq,
    selfAdjointScalarAction_neg]
  exact (selfAdjoint_reflection_eq_neg_conjugation h2 X).symm

theorem selfAdjointFullAction_range_eq_top (h2 : (2 : K) ≠ 0) :
    (selfAdjointFullAction h2).range = ⊤ := by
  let : NeZero (2 : K) := ⟨h2⟩
  let : Invertible (2 : K) := invertibleOfNonzero h2
  let : FiniteDimensional K (selfAdjointSubmodule K) :=
    Module.Finite.equiv (selfAdjointCoordinates h2)
  apply TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem
    (selfAdjointForm K) (QuadraticMap.nondegenerate_polar_iff.mp
      (selfAdjointForm_nondegenerate h2))
  intro X _
  exact selfAdjoint_reflection_mem_fullAction h2 X

theorem selfAdjointFullAction_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (selfAdjointFullAction h2) :=
  MonoidHom.range_eq_top.mp (selfAdjointFullAction_range_eq_top h2)

end CFSG.ComponentClassification.CatalogueBOrthogonalFive

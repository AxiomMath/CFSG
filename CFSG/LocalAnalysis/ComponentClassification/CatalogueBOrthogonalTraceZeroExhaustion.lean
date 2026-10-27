module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroReflection
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

@[expose] def traceZeroScalarAction :
    rootsOfUnity 2 K →* TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K) where
  toFun ε := ⟨LinearEquiv.smulOfUnit ε.val,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (by
      intro X
      change traceZeroForm K ((ε.val : K) • X) = traceZeroForm K X
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

theorem traceZeroScalarAction_val (ε : rootsOfUnity 2 K) (X : traceZeroSubmodule K) :
    ((traceZeroScalarAction ε).val X).val = (ε.val : K) • X.val := rfl

@[expose] def traceZeroNegSign (K : Type u) [Field K] : rootsOfUnity 2 K :=
  ⟨(-1 : Kˣ), by simp [mem_rootsOfUnity, pow_two]⟩

theorem traceZeroScalarAction_neg :
    traceZeroScalarAction (traceZeroNegSign K) = QuadraticMap.negOrthogonal (traceZeroForm K) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  rw [QuadraticMap.coe_negOrthogonal]
  change (-1 : K) • X = -X
  exact neg_one_smul K X

theorem traceZeroScalarAction_commute (ε : rootsOfUnity 2 K) (A : GL (Fin 2) K) :
    Commute (traceZeroScalarAction ε) (traceZeroOrthogonalAction A) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change (ε.val : K) • traceZeroConjugation A X =
    traceZeroConjugation A ((ε.val : K) • X)
  exact (traceZeroConjugation A).map_smul _ _ |>.symm

@[expose] def traceZeroFullAction :
    GL (Fin 2) K × rootsOfUnity 2 K →*
      TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K) where
  toFun x := traceZeroOrthogonalAction x.1 * traceZeroScalarAction x.2
  map_one' := by simp
  map_mul' x y := by
    change traceZeroOrthogonalAction (x.1 * y.1) * traceZeroScalarAction (x.2 * y.2) = _
    rw [map_mul, map_mul]
    exact ((traceZeroScalarAction_commute x.2 y.1).mul_mul_mul_comm _ _).symm

theorem traceZeroFullAction_val (x : GL (Fin 2) K × rootsOfUnity 2 K)
    (X : traceZeroSubmodule K) :
    ((traceZeroFullAction x).val X).val =
      (x.2.val : K) • (x.1.val * X.val * x.1⁻¹.val) := by
  change (traceZeroConjugation x.1 ((x.2.val : K) • X)).val = _
  rw [map_smul]
  rfl

theorem traceZero_reflection_mem_fullAction (X : traceZeroSubmodule K)
    [Invertible (traceZeroForm K X)] :
    TauCeti.QuadraticMap.reflectionOrthogonal (traceZeroForm K) X ∈
      (traceZeroFullAction (K := K)).range := by
  refine ⟨(traceZeroAnisotropicGL X (isUnit_of_invertible _).ne_zero,
    traceZeroNegSign K), ?_⟩
  change traceZeroOrthogonalAction _ * traceZeroScalarAction (traceZeroNegSign K) = _
  rw [← (traceZeroScalarAction_commute (traceZeroNegSign K) _).eq,
    traceZeroScalarAction_neg]
  exact (traceZero_reflection_eq_neg_conjugation X).symm

theorem traceZeroFullAction_range_eq_top (h2 : (2 : K) ≠ 0) :
    (traceZeroFullAction (K := K)).range = ⊤ := by
  let : NeZero (2 : K) := ⟨h2⟩
  let : Invertible (2 : K) := invertibleOfNonzero h2
  let : FiniteDimensional K (traceZeroSubmodule K) :=
    Module.Finite.equiv (traceZeroCoordinates K)
  apply TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem
    (traceZeroForm K) (QuadraticMap.nondegenerate_polar_iff.mp
      (traceZeroForm_nondegenerate h2))
  intro X _
  exact traceZero_reflection_mem_fullAction X

theorem traceZeroFullAction_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (traceZeroFullAction (K := K)) :=
  MonoidHom.range_eq_top.mp (traceZeroFullAction_range_eq_top h2)

end CFSG.ComponentClassification.CatalogueBOrthogonal

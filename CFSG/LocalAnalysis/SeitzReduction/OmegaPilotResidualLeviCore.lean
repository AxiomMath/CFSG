module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviSection

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.Quasithin (perfectCore perfectCore_le)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus commutator_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

theorem mul_self_eq_one_of_orderOf_plus [Finite K] (hn : 3 ≤ n)
    {s : matrixIsometries (coordinateQuadPlus n K)}
    (h : orderOf (isometryConjugationHom _ s) = 2) : s * s = 1 := by
  have hreg := regular_coordinateQuadPlus n K hn
  apply CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical.isometryKappa_injective
    hreg.1 hreg.2 (commutator_coordinateQuadPlus n K hn)
  rw [map_mul, map_one]
  change isometryConjugationHom _ s * isometryConjugationHom _ s = 1
  have h1 := pow_orderOf_eq_one (isometryConjugationHom (coordinateQuadPlus n K) s)
  rw [h, pow_two] at h1
  exact h1

variable {d : ℕ}

@[expose] noncomputable def sNil (s : GL (Fin d) K) : (Fin d → K) →ₗ[K] (Fin d → K) :=
  ((matrixLinearEquiv s : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K)) - 1

omit [CharP K 2] in
theorem sNil_apply (s : GL (Fin d) K) (v : Fin d → K) : sNil s v = matrixLinearEquiv s v - v :=
  rfl

theorem sNil_sNil {s : GL (Fin d) K} (hss : s * s = 1) (v : Fin d → K) :
    sNil s (sNil s v) = 0 := by
  have hs2 : matrixLinearEquiv s (matrixLinearEquiv s v) = v := by
    rw [← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, hss, matrixLinearEquiv_apply]
    simp
  rw [sNil_apply, sNil_apply, map_sub, hs2]
  have h0 : (2 : K) • (v - matrixLinearEquiv s v) = 0 := by
    rw [CharTwo.two_eq_zero, zero_smul]
  rw [← h0, two_smul]
  abel

theorem projLift_sNil_of_mem_core {Q : QuadraticForm K (Fin d → K)} (hQ : ∃ v, Q v ≠ 0)
    (s : matrixIsometries Q) {x : matrixProjectiveDerived Q}
    (hx : x ∈ perfectCore (autFixSubgroup (isometryConjugationHom Q s))) (v : Fin d → K) :
    projLift hQ x (sNil s.val v) = sNil s.val (projLift hQ x v) :=
  projLift_sub_one_of_mem_autFixSubgroup hQ s (perfectCore_le _ hx) v

end CFSG.SeitzReduction.OmegaPilot

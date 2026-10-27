module

public import CFSG.CharacterTheory.TwoRankLowerBound.SummandScalarTrace
public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteOrderFourier

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def restrictEndomorphismAlgHom {ring algebra vector : Type*}
    [CommRing ring] [Ring algebra] [Algebra ring algebra] [AddCommGroup vector]
    [Module ring vector] [Module algebra vector] [IsScalarTower ring algebra vector] :
    Module.End algebra vector →ₐ[ring] Module.End ring vector where
  toFun := LinearMap.restrictScalars ring
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  commutes' := fun _ => rfl

theorem periodic_summand_scalar_trace_zero {ring algebra : Type*} [CommRing ring] [IsDomain ring]
    [Ring algebra] [Algebra ring algebra] (size : ℕ) (vector : Fin size → Type*)
    [∀ label, AddCommGroup (vector label)] [∀ label, Module ring (vector label)]
    [∀ label, Module algebra (vector label)] [∀ label, IsScalarTower ring algebra (vector label)]
    [∀ label, Module.Free ring (vector label)] [∀ label, Module.Finite ring (vector label)]
    (hlocal : ∀ label, ∀ operator : Module.End algebra (vector label),
      IsUnit operator ∨ IsUnit (1 - operator))
    (scalar : algebra)
    (hzero : ∀ label, LinearMap.trace ring (vector label) (scalarActionEndomorphism ring scalar) = 0)
    (period : ℕ) (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period)
    (operator projection : Module.End algebra (∀ label, vector label))
    (hperiod : operator ^ period = 1) (hidempotent : IsIdempotentElem projection)
    (hcommute : Commute projection operator) :
    LinearMap.trace ring (∀ label, vector label)
      (((projection * operator).restrictScalars ring).comp (scalarActionEndomorphism ring scalar)) = 0 := by
  let projector := fun label : ℕ => finiteOrderEigenprojection period periodUnit (root ^ label) operator
  have hrootPeriod : root ^ period = 1 := by
    apply Units.ext
    exact hroot.pow_eq_one
  have heigenvaluePeriod : ∀ label : ℕ, (root ^ label) ^ period = 1 := by
    intro label
    rw [← pow_mul, Nat.mul_comm, pow_mul, hrootPeriod, one_pow]
  have hprojectorIdempotent : ∀ label, IsIdempotentElem (projector label) := by
    intro label
    exact finiteOrderEigenprojection_idempotent period periodUnit (root ^ label) hunit
      (heigenvaluePeriod label) operator hperiod
  have hprojectorCommute : ∀ label, Commute projection (projector label) := by
    intro label
    exact finiteOrderEigenprojection_commute period periodUnit (root ^ label) operator projection hcommute
  have hprojectorEigenvalue : ∀ label,
      operator * projector label = (↑(root ^ label) : ring) • projector label := by
    intro label
    exact finiteOrderEigenprojection_eigenvalue period periodUnit (root ^ label)
      (heigenvaluePeriod label) operator hperiod
  have hexpansion : projection * operator = ∑ label ∈ Finset.range period,
      (↑(root ^ label) : ring) • (projection * projector label) := by
    calc
      _ = projection * operator * ∑ label ∈ Finset.range period, projector label := by
        rw [finiteOrderEigenprojection_sum period periodUnit root hunit hroot, mul_one]
      _ = ∑ label ∈ Finset.range period, projection * (operator * projector label) := by
        rw [Finset.mul_sum]
        simp only [mul_assoc]
      _ = _ := by simp only [hprojectorEigenvalue, mul_smul_comm]
  have hprojectedTrace : ∀ label : ℕ, LinearMap.trace ring (∀ label, vector label)
      (((projection * projector label).restrictScalars ring).comp
        (scalarActionEndomorphism ring scalar)) = 0 := by
    intro label
    exact finite_local_summand_scalar_trace_zero size vector hlocal scalar hzero
      (projection * projector label)
      (IsIdempotentElem.mul_of_commute (hprojectorCommute label) hidempotent (hprojectorIdempotent label))
  change LinearMap.trace ring (∀ label, vector label)
    ((restrictEndomorphismAlgHom (projection * operator)).comp (scalarActionEndomorphism ring scalar)) = 0
  rw [hexpansion, map_sum]
  simp only [map_smul]
  have htraceExpansion : LinearMap.trace ring (∀ label, vector label)
      ((∑ label ∈ Finset.range period, (↑(root ^ label) : ring) •
        restrictEndomorphismAlgHom (projection * projector label)).comp
          (scalarActionEndomorphism ring scalar)) =
      ∑ label ∈ Finset.range period, (↑(root ^ label) : ring) *
        LinearMap.trace ring (∀ label, vector label)
          ((restrictEndomorphismAlgHom (projection * projector label)).comp
            (scalarActionEndomorphism ring scalar)) := by
    change LinearMap.trace ring (∀ label, vector label)
      ((∑ label ∈ Finset.range period, (↑(root ^ label) : ring) •
        restrictEndomorphismAlgHom (projection * projector label)) *
          (scalarActionEndomorphism ring scalar)) = _
    rw [Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul, smul_eq_mul, Module.End.mul_eq_comp]
  rw [htraceExpansion]
  apply Finset.sum_eq_zero
  intro label _
  change (↑(root ^ label) : ring) * LinearMap.trace ring (∀ label, vector label)
    (((projection * projector label).restrictScalars ring).comp
      (scalarActionEndomorphism ring scalar)) = 0
  rw [hprojectedTrace label, mul_zero]

end CFSG.TwoRankLowerBound.Helpers

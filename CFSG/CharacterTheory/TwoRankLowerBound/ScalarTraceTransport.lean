module

public import CFSG.CharacterTheory.TwoRankLowerBound.PeriodicSummandTrace

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem projected_scalar_trace_equiv {ring algebra vector target : Type*}
    [CommRing ring] [CommRing algebra] [Algebra ring algebra]
    [AddCommGroup vector] [Module ring vector] [Module algebra vector]
    [IsScalarTower ring algebra vector] [AddCommGroup target] [Module ring target]
    [Module algebra target] [IsScalarTower ring algebra target]
    (equivalence : vector ≃ₗ[algebra] target) (operator : Module.End algebra vector) (scalar : algebra) :
    LinearMap.trace ring vector ((operator.restrictScalars ring).comp
      (scalarActionEndomorphism ring scalar)) =
      LinearMap.trace ring target ((((LinearEquiv.conjAlgEquiv ring equivalence) operator).restrictScalars ring).comp
        (scalarActionEndomorphism ring scalar)) := by
  rw [← LinearMap.trace_conj' _ (equivalence.restrictScalars ring)]
  congr 1
  apply LinearMap.ext
  intro value
  change equivalence (operator (scalar • equivalence.symm value)) =
    equivalence (operator (equivalence.symm (scalar • value)))
  rw [equivalence.symm.map_smul]

theorem finiteIndex_local_summand_scalar_trace_zero {ring algebra index : Type*}
    [CommRing ring] [CommRing algebra] [Algebra ring algebra] [Finite index] (vector : index → Type*)
    [∀ label, AddCommGroup (vector label)] [∀ label, Module ring (vector label)]
    [∀ label, Module algebra (vector label)] [∀ label, IsScalarTower ring algebra (vector label)]
    [∀ label, Module.Free ring (vector label)] [∀ label, Module.Finite ring (vector label)]
    (hlocal : ∀ label, ∀ operator : Module.End algebra (vector label),
      IsUnit operator ∨ IsUnit (1 - operator)) (scalar : algebra)
    (hzero : ∀ label, LinearMap.trace ring (vector label) (scalarActionEndomorphism ring scalar) = 0)
    (projection : Module.End algebra (∀ label, vector label))
    (hidempotent : IsIdempotentElem projection) :
    LinearMap.trace ring (∀ label, vector label) ((projection.restrictScalars ring).comp
      (scalarActionEndomorphism ring scalar)) = 0 := by
  let := Fintype.ofFinite index
  let labels := (Fintype.equivFin index).symm
  let equivalence := (LinearEquiv.piCongrLeft algebra vector labels).symm
  rw [projected_scalar_trace_equiv equivalence projection scalar]
  exact finite_local_summand_scalar_trace_zero (Fintype.card index)
    (fun label => vector (labels label)) (fun label => hlocal (labels label)) scalar
    (fun label => hzero (labels label)) ((LinearEquiv.conjAlgEquiv ring equivalence) projection)
    (by
      change (LinearEquiv.conjAlgEquiv ring equivalence) projection *
        (LinearEquiv.conjAlgEquiv ring equivalence) projection =
          (LinearEquiv.conjAlgEquiv ring equivalence) projection
      rw [← map_mul]
      exact congrArg (LinearEquiv.conjAlgEquiv ring equivalence) hidempotent.eq)

theorem finiteIndex_periodic_summand_scalar_trace_zero {ring algebra index : Type*}
    [CommRing ring] [IsDomain ring] [CommRing algebra] [Algebra ring algebra] [Finite index]
    (vector : index → Type*)
    [∀ label, AddCommGroup (vector label)] [∀ label, Module ring (vector label)]
    [∀ label, Module algebra (vector label)] [∀ label, IsScalarTower ring algebra (vector label)]
    [∀ label, Module.Free ring (vector label)] [∀ label, Module.Finite ring (vector label)]
    (hlocal : ∀ label, ∀ operator : Module.End algebra (vector label),
      IsUnit operator ∨ IsUnit (1 - operator)) (scalar : algebra)
    (hzero : ∀ label, LinearMap.trace ring (vector label) (scalarActionEndomorphism ring scalar) = 0)
    (period : ℕ) (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period)
    (operator projection : Module.End algebra (∀ label, vector label))
    (hperiod : operator ^ period = 1) (hidempotent : IsIdempotentElem projection)
    (hcommute : Commute projection operator) :
    LinearMap.trace ring (∀ label, vector label)
      (((projection * operator).restrictScalars ring).comp (scalarActionEndomorphism ring scalar)) = 0 := by
  let := Fintype.ofFinite index
  let labels := (Fintype.equivFin index).symm
  let equivalence := (LinearEquiv.piCongrLeft algebra vector labels).symm
  rw [projected_scalar_trace_equiv equivalence (projection * operator) scalar, map_mul]
  apply periodic_summand_scalar_trace_zero (Fintype.card index)
    (fun label => vector (labels label)) (fun label => hlocal (labels label)) scalar
    (fun label => hzero (labels label)) period periodUnit root hunit hroot
  · rw [← map_pow, hperiod, map_one]
  · change (LinearEquiv.conjAlgEquiv ring equivalence) projection *
      (LinearEquiv.conjAlgEquiv ring equivalence) projection =
        (LinearEquiv.conjAlgEquiv ring equivalence) projection
    rw [← map_mul]
    exact congrArg (LinearEquiv.conjAlgEquiv ring equivalence) hidempotent.eq
  · exact hcommute.map (LinearEquiv.conjAlgEquiv ring equivalence)

end CFSG.TwoRankLowerBound.Helpers

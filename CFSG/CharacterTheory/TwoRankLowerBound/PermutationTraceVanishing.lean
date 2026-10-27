module

public import CFSG.CharacterTheory.TwoRankLowerBound.OrbitPermutationTrace

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def permutationEquivariantEndomorphism {ring group points : Type*} [CommRing ring]
    [Group group] [MulAction group points] (operator : Module.End ring (MonoidAlgebra ring points))
    (hequivariant : ∀ element : group, Commute operator (Representation.ofMulAction ring group points element)) :
    Module.End (MonoidAlgebra ring group) (Representation.ofMulAction ring group points).asModule := by
  let representation := Representation.ofMulAction ring group points
  let equivalence := representation.asModuleEquiv
  let transported := (LinearEquiv.conjAlgEquiv ring equivalence.symm) operator
  apply MonoidAlgebra.equivariantOfLinearOfComm transported
  intro element value
  apply equivalence.injective
  change operator (equivalence ((MonoidAlgebra.single element 1 : MonoidAlgebra ring group) • value)) =
    equivalence ((MonoidAlgebra.single element 1 : MonoidAlgebra ring group) •
      equivalence.symm (operator (equivalence value)))
  rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one,
    equivalence.apply_symm_apply]
  exact congrArg (fun endomorphism : Module.End ring (MonoidAlgebra ring points) => endomorphism (equivalence value))
    (hequivariant element).eq

theorem permutationEquivariantEndomorphism_apply {ring group points : Type*} [CommRing ring]
    [Group group] [MulAction group points] (operator : Module.End ring (MonoidAlgebra ring points))
    (hequivariant : ∀ element : group, Commute operator (Representation.ofMulAction ring group points element))
    (value : (Representation.ofMulAction ring group points).asModule) :
    permutationEquivariantEndomorphism operator hequivariant value =
      (Representation.ofMulAction ring group points).asModuleEquiv.symm
        (operator ((Representation.ofMulAction ring group points).asModuleEquiv value)) := rfl

theorem permutationEquivariantEndomorphism_restrict {ring group points : Type*} [CommRing ring]
    [Group group] [MulAction group points] (operator : Module.End ring (MonoidAlgebra ring points))
    (hequivariant : ∀ element : group, Commute operator (Representation.ofMulAction ring group points element)) :
    (permutationEquivariantEndomorphism operator hequivariant).restrictScalars ring =
      (LinearEquiv.conjAlgEquiv ring (Representation.ofMulAction ring group points).asModuleEquiv.symm) operator := rfl

theorem finite_p_action_equivariant_summand_trace_zero {ring group points : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [CommGroup group] [Finite group]
    [MulAction group points] [Finite points] (prime : ℕ) [Fact prime.Prime]
    [CharP (IsLocalRing.ResidueField ring) prime] (hgroup : IsPGroup prime group)
    (element : group) (hfixedpointFree : ∀ point : points, element • point ≠ point)
    (period : ℕ) (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period)
    (operator projection : Module.End ring (MonoidAlgebra ring points))
    (hoperator : ∀ member : group, Commute operator (Representation.ofMulAction ring group points member))
    (hprojection : ∀ member : group, Commute projection (Representation.ofMulAction ring group points member))
    (hperiod : operator ^ period = 1) (hidempotent : IsIdempotentElem projection)
    (hcommute : Commute projection operator) :
    LinearMap.trace ring (MonoidAlgebra ring points)
      (projection * operator * Representation.ofMulAction ring group points element) = 0 := by
  let equivalence := (Representation.ofMulAction ring group points).asModuleEquiv
  let liftedOperator := permutationEquivariantEndomorphism operator hoperator
  let liftedProjection := permutationEquivariantEndomorphism projection hprojection
  have hfaithful : Function.Injective
      (restrictEndomorphismAlgHom (ring := ring)
        (algebra := MonoidAlgebra ring group)
        (vector := (Representation.ofMulAction ring group points).asModule)) := by
    intro left right hequal
    exact LinearMap.ext (fun value => congrArg (fun endomorphism => endomorphism value) hequal)
  have hliftPeriod : liftedOperator ^ period = 1 := by
    apply hfaithful
    change restrictEndomorphismAlgHom (liftedOperator ^ period) = restrictEndomorphismAlgHom 1
    rw [map_pow, map_one]
    change ((LinearEquiv.conjAlgEquiv ring equivalence.symm) operator) ^ period = 1
    rw [← map_pow, hperiod, map_one]
  have hliftIdempotent : IsIdempotentElem liftedProjection := by
    change liftedProjection * liftedProjection = liftedProjection
    apply hfaithful
    rw [map_mul]
    change (LinearEquiv.conjAlgEquiv ring equivalence.symm) projection *
      (LinearEquiv.conjAlgEquiv ring equivalence.symm) projection =
        (LinearEquiv.conjAlgEquiv ring equivalence.symm) projection
    rw [← map_mul]
    exact congrArg (LinearEquiv.conjAlgEquiv ring equivalence.symm) hidempotent.eq
  have hliftCommute : Commute liftedProjection liftedOperator := by
    apply hfaithful
    rw [map_mul, map_mul]
    exact hcommute.map (LinearEquiv.conjAlgEquiv ring equivalence.symm) |>.eq
  have htrace := finite_p_action_periodic_summand_trace_zero prime hgroup element hfixedpointFree
    period periodUnit root hunit hroot liftedOperator liftedProjection hliftPeriod hliftIdempotent hliftCommute
  have htransport : (LinearEquiv.conjAlgEquiv ring equivalence)
      (((liftedProjection * liftedOperator).restrictScalars ring).comp
        (scalarActionEndomorphism ring (MonoidAlgebra.single element 1 : MonoidAlgebra ring group))) =
      projection * operator * Representation.ofMulAction ring group points element := by
    apply LinearMap.ext
    intro value
    change projection (operator (equivalence
      ((MonoidAlgebra.single element 1 : MonoidAlgebra ring group) • equivalence.symm value))) = _
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one,
      equivalence.apply_symm_apply]
    rfl
  rw [← htransport]
  exact (LinearMap.trace_conj' _ equivalence).trans htrace

end CFSG.TwoRankLowerBound.Helpers

module

public import CFSG.CharacterTheory.TwoRankLowerBound.OrbitModuleEquiv
public import CFSG.CharacterTheory.TwoRankLowerBound.ScalarTraceTransport

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem finite_p_action_periodic_summand_trace_zero {ring group points : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [CommGroup group] [Finite group]
    [MulAction group points] [Finite points] (prime : ℕ) [Fact prime.Prime]
    [CharP (IsLocalRing.ResidueField ring) prime] (hgroup : IsPGroup prime group)
    (element : group) (hfixedpointFree : ∀ point : points, element • point ≠ point)
    (period : ℕ) (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period)
    (operator projection : Module.End (MonoidAlgebra ring group)
      (Representation.ofMulAction ring group points).asModule)
    (hperiod : operator ^ period = 1) (hidempotent : IsIdempotentElem projection)
    (hcommute : Commute projection operator) :
    LinearMap.trace ring (Representation.ofMulAction ring group points).asModule
      (((projection * operator).restrictScalars ring).comp
        (scalarActionEndomorphism ring (MonoidAlgebra.single element 1 : MonoidAlgebra ring group))) = 0 := by
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient group points)
  let : ∀ orbit : MulAction.orbitRel.Quotient group points,
      Module (MonoidAlgebra ring group) (MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out)) :=
    fun orbit => Module.compHom (MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out))
      (MonoidAlgebra.mapDomainRingHom ring (QuotientGroup.mk' (MulAction.stabilizer group orbit.out)))
  let : ∀ orbit : MulAction.orbitRel.Quotient group points,
      IsScalarTower ring (MonoidAlgebra ring group)
        (MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out)) :=
    fun orbit => groupAlgebra_quotient_scalarTower (QuotientGroup.mk' (MulAction.stabilizer group orbit.out))
  let equivalence := orbitPermutationModuleEquiv (ring := ring) (group := group) (points := points)
  rw [projected_scalar_trace_equiv equivalence (projection * operator), map_mul]
  apply finiteIndex_periodic_summand_scalar_trace_zero
    (fun orbit : MulAction.orbitRel.Quotient group points =>
      MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out))
    (fun orbit => abelianQuotientGroupAlgebra_endomorphism_unit_or_complement prime hgroup
      (MulAction.stabilizer group orbit.out))
    (MonoidAlgebra.single element 1)
    (fun orbit => quotientGroupAlgebra_nonidentity_scalar_trace
      (QuotientGroup.mk' (MulAction.stabilizer group orbit.out)) element (by
        intro hequal
        have hmember := (QuotientGroup.eq_one_iff element).mp hequal
        exact hfixedpointFree orbit.out (MulAction.mem_stabilizer_iff.mp hmember)))
    period periodUnit root hunit hroot
  · rw [← map_pow, hperiod, map_one]
  · change (LinearEquiv.conjAlgEquiv ring equivalence) projection *
      (LinearEquiv.conjAlgEquiv ring equivalence) projection =
        (LinearEquiv.conjAlgEquiv ring equivalence) projection
    rw [← map_mul]
    exact congrArg (LinearEquiv.conjAlgEquiv ring equivalence) hidempotent.eq
  · exact hcommute.map (LinearEquiv.conjAlgEquiv ring equivalence)

end CFSG.TwoRankLowerBound.Helpers

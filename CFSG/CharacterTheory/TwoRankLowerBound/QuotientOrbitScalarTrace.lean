module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuotientGroupAlgebraEndomorphisms
public import CFSG.CharacterTheory.TwoRankLowerBound.PeriodicSummandTrace

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupAlgebra_quotient_scalarTower {ring source target : Type*} [CommRing ring]
    [Group source] [CommGroup target] (quotient : source →* target) :
    letI := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
    IsScalarTower ring (MonoidAlgebra ring source) (MonoidAlgebra ring target) := by
  let := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
  apply IsScalarTower.of_algebraMap_smul
  intro coefficient value
  change MonoidAlgebra.mapDomainRingHom ring quotient
    (algebraMap ring (MonoidAlgebra ring source) coefficient) * value = coefficient • value
  have hequal := congrArg (fun homomorphism : ring →+* MonoidAlgebra ring target => homomorphism coefficient)
    (MonoidAlgebra.mapDomainRingHom_comp_algebraMap (R := ring) (A := ring) quotient)
  change MonoidAlgebra.mapDomainRingHom ring quotient
    (algebraMap ring (MonoidAlgebra ring source) coefficient) =
      algebraMap ring (MonoidAlgebra ring target) coefficient at hequal
  rw [hequal, Algebra.smul_def]

theorem quotientGroupAlgebra_nonidentity_scalar_trace {ring source target : Type*}
    [CommRing ring] [Group source] [CommGroup target] [Finite target]
    (quotient : source →* target) (element : source) (hnonidentity : quotient element ≠ 1) :
    letI := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
    letI := groupAlgebra_quotient_scalarTower (ring := ring) quotient
    LinearMap.trace ring (MonoidAlgebra ring target)
      (scalarActionEndomorphism ring (MonoidAlgebra.single element 1 : MonoidAlgebra ring source)) = 0 := by
  let := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
  let := groupAlgebra_quotient_scalarTower (ring := ring) quotient
  have hoperator : scalarActionEndomorphism ring
      (MonoidAlgebra.single element 1 : MonoidAlgebra ring source) =
      Algebra.lmul ring (MonoidAlgebra ring target) (MonoidAlgebra.single (quotient element) 1) := by
    apply LinearMap.ext
    intro value
    change MonoidAlgebra.mapDomainRingHom ring quotient (MonoidAlgebra.single element 1) * value = _
    simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
    rfl
  rw [hoperator]
  exact groupAlgebra_nonidentity_translation_trace _ hnonidentity

theorem quotientOrbit_periodic_summand_trace_zero {ring group : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [CommGroup group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime group) (size : ℕ) (subgroup : Fin size → Subgroup group)
    (element : group) (hfixedpointFree : ∀ label, QuotientGroup.mk' (subgroup label) element ≠ 1)
    (period : ℕ) (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period) :
    letI : ∀ label, Module (MonoidAlgebra ring group) (MonoidAlgebra ring (group ⧸ subgroup label)) :=
      fun label => Module.compHom (MonoidAlgebra ring (group ⧸ subgroup label))
        (MonoidAlgebra.mapDomainRingHom ring (QuotientGroup.mk' (subgroup label)))
    letI : ∀ label, IsScalarTower ring (MonoidAlgebra ring group)
      (MonoidAlgebra ring (group ⧸ subgroup label)) :=
      fun label => groupAlgebra_quotient_scalarTower (QuotientGroup.mk' (subgroup label))
    ∀ operator projection : Module.End (MonoidAlgebra ring group)
      (∀ label, MonoidAlgebra ring (group ⧸ subgroup label)),
      operator ^ period = 1 → IsIdempotentElem projection → Commute projection operator →
      LinearMap.trace ring (∀ label, MonoidAlgebra ring (group ⧸ subgroup label))
        (((projection * operator).restrictScalars ring).comp
          (scalarActionEndomorphism ring (MonoidAlgebra.single element 1 : MonoidAlgebra ring group))) = 0 := by
  let : ∀ label, Module (MonoidAlgebra ring group) (MonoidAlgebra ring (group ⧸ subgroup label)) :=
    fun label => Module.compHom (MonoidAlgebra ring (group ⧸ subgroup label))
      (MonoidAlgebra.mapDomainRingHom ring (QuotientGroup.mk' (subgroup label)))
  let : ∀ label, IsScalarTower ring (MonoidAlgebra ring group)
      (MonoidAlgebra ring (group ⧸ subgroup label)) :=
    fun label => groupAlgebra_quotient_scalarTower (QuotientGroup.mk' (subgroup label))
  intro operator projection hperiod hidempotent hcommute
  exact periodic_summand_scalar_trace_zero size
    (fun label => MonoidAlgebra ring (group ⧸ subgroup label))
    (fun label => abelianQuotientGroupAlgebra_endomorphism_unit_or_complement prime hgroup (subgroup label))
    (MonoidAlgebra.single element 1)
    (fun label => quotientGroupAlgebra_nonidentity_scalar_trace
      (QuotientGroup.mk' (subgroup label)) element (hfixedpointFree label))
    period periodUnit root hunit hroot operator projection hperiod hidempotent hcommute

end CFSG.TwoRankLowerBound.Helpers

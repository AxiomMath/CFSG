module

public import CFSG.CharacterTheory.TwoRankLowerBound.GroupAlgebraUnitResidue
public import CFSG.CharacterTheory.TwoRankLowerBound.QuotientRegularEndomorphisms

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupAlgebra_mapDomain_surjective {ring source target : Type*} [Semiring ring]
    [Monoid source] [Monoid target] (quotient : source →* target)
    (hsurjective : Function.Surjective quotient) :
    Function.Surjective (MonoidAlgebra.mapDomainRingHom ring quotient) := by
  intro value
  obtain ⟨coefficients, hcoefficients⟩ := Finsupp.mapDomain_surjective hsurjective value.coeff
  refine ⟨MonoidAlgebra.ofCoeff coefficients, ?_⟩
  ext element
  simpa only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain,
    MonoidAlgebra.coeff_ofCoeff] using congrArg (fun function => function element) hcoefficients

@[expose] noncomputable def quotientGroupAlgebraEndomorphismEquiv {ring source target : Type*}
    [CommRing ring] [Group source] [CommGroup target] (quotient : source →* target)
    (hsurjective : Function.Surjective quotient) :
    letI := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
    MonoidAlgebra ring target ≃+* Module.End (MonoidAlgebra ring source) (MonoidAlgebra ring target) := by
  letI := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
  exact quotientRegularEndomorphismEquiv (MonoidAlgebra.mapDomainRingHom ring quotient)
    (fun _ _ => rfl) (groupAlgebra_mapDomain_surjective quotient hsurjective)

theorem quotientGroupAlgebraEndomorphismEquiv_apply {ring source target : Type*}
    [CommRing ring] [Group source] [CommGroup target] (quotient : source →* target)
    (hsurjective : Function.Surjective quotient) (coefficient value : MonoidAlgebra ring target) :
    quotientGroupAlgebraEndomorphismEquiv quotient hsurjective coefficient value = coefficient * value := rfl

theorem quotientGroupAlgebra_endomorphism_unit_or_complement {ring source target : Type*}
    [CommRing ring] [IsLocalRing ring] [Group source] [CommGroup target] [Finite target]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime target) (quotient : source →* target)
    (hsurjective : Function.Surjective quotient) :
    letI := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
    ∀ operator : Module.End (MonoidAlgebra ring source) (MonoidAlgebra ring target),
      IsUnit operator ∨ IsUnit (1 - operator) := by
  let := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
  intro operator
  exact quotientRegular_endomorphism_unit_or_complement
    (MonoidAlgebra.mapDomainRingHom ring quotient) (fun _ _ => rfl)
    (groupAlgebra_mapDomain_surjective quotient hsurjective)
    (local_abelian_p_group_algebra_unit_or_complement prime hgroup) operator

@[expose] noncomputable def abelianQuotientGroupAlgebraEndomorphismEquiv {ring group : Type*}
    [CommRing ring] [CommGroup group] (subgroup : Subgroup group) :
    letI := Module.compHom (MonoidAlgebra ring (group ⧸ subgroup))
      (MonoidAlgebra.mapDomainRingHom ring (QuotientGroup.mk' subgroup))
    MonoidAlgebra ring (group ⧸ subgroup) ≃+*
      Module.End (MonoidAlgebra ring group) (MonoidAlgebra ring (group ⧸ subgroup)) :=
  quotientGroupAlgebraEndomorphismEquiv (QuotientGroup.mk' subgroup)
    (QuotientGroup.mk'_surjective subgroup)

theorem abelianQuotientGroupAlgebra_endomorphism_unit_or_complement {ring group : Type*}
    [CommRing ring] [IsLocalRing ring] [CommGroup group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime group) (subgroup : Subgroup group) :
    letI := Module.compHom (MonoidAlgebra ring (group ⧸ subgroup))
      (MonoidAlgebra.mapDomainRingHom ring (QuotientGroup.mk' subgroup))
    ∀ operator : Module.End (MonoidAlgebra ring group) (MonoidAlgebra ring (group ⧸ subgroup)),
      IsUnit operator ∨ IsUnit (1 - operator) :=
  quotientGroupAlgebra_endomorphism_unit_or_complement prime (hgroup.to_quotient subgroup)
    (QuotientGroup.mk' subgroup) (QuotientGroup.mk'_surjective subgroup)

end CFSG.TwoRankLowerBound.Helpers

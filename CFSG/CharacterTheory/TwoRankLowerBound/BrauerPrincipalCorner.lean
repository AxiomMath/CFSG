module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerBimoduleReduction
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalAverageQuotient

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem p_centralizer_projection_augmentation {field group : Type*}
    [Field field] [Group group] [Fintype group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (subgroup : Subgroup group) (hgroup : IsPGroup prime subgroup) (value : MonoidAlgebra field group)
    (hinvariant : subgroupConjugationInvariant subgroup value) :
    groupAlgebraAugmentation field (Subgroup.centralizer (subgroup : Set group))
      (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)) value) =
      groupAlgebraAugmentation field group value := by
  let : MulAction subgroup group := subgroupConjugationAction subgroup
  rw [groupAlgebraAugmentation_sum, groupAlgebraAugmentation_sum]
  simp only [subgroupCoefficientProjection_coeff]
  have hequal := p_group_invariant_sum_fixedPoints prime hgroup (fun element => value.coeff element)
    (fun element member => hinvariant element member)
  simp only [conjugation_fixedPoints_iff_centralizer] at hequal
  rw [hequal, ← Finset.sum_filter]
  symm
  apply Finset.sum_subtype
  intro member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem normalSubgroupAverage_augmentation {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group) [Fintype subgroup]
    (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card subgroup) :
    groupAlgebraAugmentation ring group (normalSubgroupAverage subgroup cardUnit) = 1 := by
  unfold normalSubgroupAverage
  change groupAlgebraAugmentation ring group
    (((cardUnit⁻¹ : ringˣ) : ring) • (∑ member : subgroup,
      MonoidAlgebra.single member.val 1 : MonoidAlgebra ring group)) = 1
  rw [groupAlgebraAugmentation_sum]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hsum : ∑ member : subgroup, ∑ element : group,
      (MonoidAlgebra.single member.val (1 : ring)).coeff element = Nat.card subgroup := by
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  rw [hsum, ← hcard, Units.inv_mul]

theorem normalSubgroupAverage_map_ringHom {ring target group : Type*}
    [CommRing ring] [CommRing target] [Group group] [Fintype group]
    (subgroup : Subgroup group) [Fintype subgroup] (cardUnit : ringˣ) (embedding : ring →+* target) :
    MonoidAlgebra.mapRingHom group embedding (normalSubgroupAverage subgroup cardUnit) =
      normalSubgroupAverage subgroup (Units.map embedding.toMonoidHom cardUnit) := by
  ext element
  simp only [MonoidAlgebra.coeff_mapRingHom, normalSubgroupAverage, MonoidAlgebra.coeff_smul_apply,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  change embedding ((↑(cardUnit⁻¹) : ring) * ∑ member : subgroup,
      (MonoidAlgebra.single member.val (1 : ring)).coeff element) =
    embedding (↑(cardUnit⁻¹)) * ∑ member : subgroup,
      (MonoidAlgebra.single member.val (1 : target)).coeff element
  rw [map_mul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro member _
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp only [map_one, map_zero]

theorem field_normal_average_idempotent_eq_zero_or_average {field source target : Type*}
    [Field field] [Group source] [Fintype source] [Group target] [Finite target]
    (quotient : source →* target) (hsurjective : Function.Surjective quotient)
    [Fintype quotient.ker] (cardUnit : fieldˣ) (hcard : (cardUnit : field) = Nat.card quotient.ker)
    (prime : ℕ) [Fact prime.Prime] [CharP field prime] (hgroup : IsPGroup prime target)
    (value : MonoidAlgebra field source) (hidempotent : IsIdempotentElem value)
    (hsupport : normalSubgroupAverage quotient.ker cardUnit * value = value) :
    value = 0 ∨ value = normalSubgroupAverage quotient.ker cardUnit := by
  let pushed := MonoidAlgebra.mapDomainRingHom field quotient value
  have hunits : IsUnit pushed ∨ IsUnit (1 - pushed) := by
    rw [p_group_algebra_isUnit_iff prime hgroup, p_group_algebra_isUnit_iff prime hgroup, map_sub, map_one]
    by_cases hzero : groupAlgebraAugmentation field target pushed = 0
    · right
      rw [hzero, sub_zero]
      exact one_ne_zero
    · exact Or.inl hzero
  rcases idempotent_eq_zero_or_one_of_unit_or_complement pushed
    (hidempotent.map (MonoidAlgebra.mapDomainRingHom field quotient)) hunits with hzero | hone
  · left
    change MonoidAlgebra.mapDomainRingHom field quotient value = 0 at hzero
    rw [← hsupport, ← normalAverageQuotientSection_mapDomain quotient hsurjective cardUnit,
      hzero, map_zero]
  · right
    change MonoidAlgebra.mapDomainRingHom field quotient value = 1 at hone
    have haverage := normalAverageQuotientSection_mapDomain quotient hsurjective cardUnit
      (normalSubgroupAverage quotient.ker cardUnit)
    rw [normalSubgroupAverage_mapDomain quotient cardUnit hcard,
      (normalSubgroupAverage_idempotent quotient.ker cardUnit hcard).eq] at haverage
    rw [← hsupport, ← normalAverageQuotientSection_mapDomain quotient hsurjective cardUnit, hone, haverage]

theorem residue_centralizer_normalComplement_corner {ring field group quotientGroup : Type*}
    [CommRing ring] [Field field] [Group group] [Fintype group]
    [Group quotientGroup] [Finite quotientGroup]
    (embedding : ring →+* field) (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (subgroup : Subgroup group) (hsubgroup : IsPGroup prime subgroup)
    (quotient : Subgroup.centralizer (subgroup : Set group) →* quotientGroup)
    (hsurjective : Function.Surjective quotient) (hquotient : IsPGroup prime quotientGroup)
    [Fintype quotient.ker] (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card quotient.ker)
    (value : MonoidAlgebra ring group) (hidempotent : IsIdempotentElem value)
    (hinvariant : subgroupConjugationInvariant subgroup value) :
    MonoidAlgebra.mapRingHom (Subgroup.centralizer (subgroup : Set group)) embedding
      (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)) value *
        normalSubgroupAverage quotient.ker cardUnit) =
      (embedding (groupAlgebraAugmentation ring group value)) •
        MonoidAlgebra.mapRingHom (Subgroup.centralizer (subgroup : Set group)) embedding
          (normalSubgroupAverage quotient.ker cardUnit) := by
  let reduced := MonoidAlgebra.mapRingHom group embedding value
  let projected := subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)) reduced
  let residueCard := Units.map embedding.toMonoidHom cardUnit
  let average := normalSubgroupAverage quotient.ker residueCard
  have hresidueCard : (residueCard : field) = Nat.card quotient.ker := by
    change embedding (cardUnit : ring) = _
    rw [hcard, map_natCast]
  have hreducedInvariant : subgroupConjugationInvariant subgroup reduced := by
    intro element member
    simp only [reduced, MonoidAlgebra.coeff_mapRingHom]
    rw [hinvariant]
  have hprojectedIdempotent : IsIdempotentElem projected := by
    change projected * projected = projected
    rw [← prime_centralizer_coefficientProjection_mul prime subgroup hsubgroup reduced reduced
      hreducedInvariant hreducedInvariant]
    exact congrArg (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)))
      (hidempotent.map (MonoidAlgebra.mapRingHom group embedding)).eq
  have haverageIdempotent : IsIdempotentElem average :=
    normalSubgroupAverage_idempotent quotient.ker residueCard hresidueCard
  have hproductIdempotent : IsIdempotentElem (projected * average) :=
    IsIdempotentElem.mul_of_commute (normalSubgroupAverage_central quotient.ker residueCard projected).symm
      hprojectedIdempotent haverageIdempotent
  have hcorner : average * (projected * average) = projected * average := by
    rw [← mul_assoc, (normalSubgroupAverage_central quotient.ker residueCard projected).eq, mul_assoc,
      haverageIdempotent.eq]
  have haugmentation := p_centralizer_projection_augmentation prime subgroup hsubgroup reduced hreducedInvariant
  have haverageAugmentation := normalSubgroupAverage_augmentation quotient.ker residueCard hresidueCard
  have hproduct : projected * average =
      (groupAlgebraAugmentation field group reduced) • average := by
    rcases field_normal_average_idempotent_eq_zero_or_average quotient hsurjective residueCard hresidueCard
      prime hquotient (projected * average) hproductIdempotent hcorner with hzero | hone
    · have hequal := congrArg
        (groupAlgebraAugmentation field (Subgroup.centralizer (subgroup : Set group))) hzero
      rw [map_mul, haverageAugmentation, mul_one, haugmentation, map_zero] at hequal
      rw [hzero, hequal, zero_smul]
    · have hequal := congrArg
        (groupAlgebraAugmentation field (Subgroup.centralizer (subgroup : Set group))) hone
      rw [map_mul, haverageAugmentation, mul_one, haugmentation] at hequal
      rw [hone, hequal, one_smul]
  rw [map_mul, ← subgroupCoefficientProjection_map_coefficients,
    normalSubgroupAverage_map_ringHom]
  rw [groupAlgebraAugmentation_map] at hproduct
  exact hproduct

end CFSG.TwoRankLowerBound.Helpers

module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralSubgroupProjection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem centralizer_conjugation_mem_iff {G : Type*} [Group G]
    (subgroup : Subgroup G) (conjugator element : G)
    (hnormalizes : conjugator ∈ Subgroup.normalizer (subgroup : Set G)) :
    conjugator * element * conjugator⁻¹ ∈ Subgroup.centralizer (subgroup : Set G) ↔
      element ∈ Subgroup.centralizer (subgroup : Set G) := by
  have hforward (conjugator element : G)
      (hnormalizes : conjugator ∈ Subgroup.normalizer (subgroup : Set G))
      (helement : element ∈ Subgroup.centralizer (subgroup : Set G)) :
      conjugator * element * conjugator⁻¹ ∈ Subgroup.centralizer (subgroup : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    have hconjugate : conjugator⁻¹ * member * conjugator ∈ subgroup :=
      (Subgroup.mem_normalizer_iff''.mp hnormalizes member).mp hmember
    have hcommute := Subgroup.mem_centralizer_iff.mp helement _ hconjugate
    have hequal := congrArg (fun value => conjugator * value * conjugator⁻¹) hcommute
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel_right, mul_inv_cancel, mul_one] using hequal
  constructor
  · intro helement
    have hresult := hforward conjugator⁻¹ (conjugator * element * conjugator⁻¹)
      ((Subgroup.normalizer (subgroup : Set G)).inv_mem hnormalizes) helement
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
      inv_mul_cancel, mul_one] using hresult
  · exact hforward conjugator element hnormalizes

@[expose] noncomputable def normalizerCentralizerCoefficientProjection {ring G : Type*}
    [CommRing ring] [Group G] [Fintype G] (subgroup intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate) :
    MonoidAlgebra ring G →ₗ[ring] MonoidAlgebra ring intermediate :=
  (MonoidAlgebra.mapDomainAlgHom ring ring (Subgroup.inclusion hcontains)).toLinearMap.comp
    (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set G)))

theorem normalizerCentralizerCoefficientProjection_coeff {ring G : Type*}
    [CommRing ring] [Group G] [Fintype G] (subgroup intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (value : MonoidAlgebra ring G) (element : intermediate) :
    (normalizerCentralizerCoefficientProjection subgroup intermediate hcontains value).coeff element =
      if element.val ∈ Subgroup.centralizer (subgroup : Set G) then value.coeff element.val else 0 := by
  by_cases hmember : element.val ∈ Subgroup.centralizer (subgroup : Set G)
  · let member : Subgroup.centralizer (subgroup : Set G) := ⟨element.val, hmember⟩
    have helement : Subgroup.inclusion hcontains member = element := Subtype.ext rfl
    rw [ite_eq_left hmember, ← helement]
    change (MonoidAlgebra.mapDomainRingHom ring (Subgroup.inclusion hcontains)
      (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set G)) value)).coeff
        (Subgroup.inclusion hcontains member) = value.coeff member.val
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain,
      Finsupp.mapDomain_apply_of_injective (Subgroup.inclusion_injective hcontains),
      subgroupCoefficientProjection_coeff]
  · rw [ite_eq_right hmember]
    change (MonoidAlgebra.mapDomainRingHom ring (Subgroup.inclusion hcontains)
      (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set G)) value)).coeff element = 0
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨member, hequal⟩
    exact hmember ((congrArg Subtype.val hequal) ▸ member.property)

theorem normalizerCentralizerCoefficientProjection_one {ring G : Type*}
    [CommRing ring] [Group G] [Fintype G] (subgroup intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate) :
    normalizerCentralizerCoefficientProjection subgroup intermediate hcontains
      (1 : MonoidAlgebra ring G) = 1 := by
  change MonoidAlgebra.mapDomainRingHom ring (Subgroup.inclusion hcontains)
    (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set G)) 1) = 1
  rw [subgroupCoefficientProjection_one, map_one]

@[expose] noncomputable def centralNormalizerCoefficientProjection {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) (subgroup intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (subgroup : Set G)) :
    centralCoefficientSubring (G := G) ring →+ centralCoefficientSubring (G := intermediate) ring where
  toFun value := ⟨normalizerCentralizerCoefficientProjection subgroup intermediate hcontains value.val, by
    constructor
    · intro element
      rw [normalizerCentralizerCoefficientProjection_coeff]
      split_ifs
      · exact centralCoefficientSubring_coefficients ring value element.val
      · exact ring.zero_mem
    · apply Subring.mem_center_iff.mpr
      intro other
      apply Commute.symm
      apply groupAlgebra_central_of_coeff_conjugation
      intro element conjugator
      simp only [normalizerCentralizerCoefficientProjection_coeff, Subgroup.coe_mul, Subgroup.coe_inv,
        centralizer_conjugation_mem_iff subgroup conjugator.val element.val
          (hnormalizes conjugator.property),
        central_groupAlgebra_coeff_conjugation value.val (centralCoefficientSubring_commutes ring value)]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' left right := Subtype.ext (map_add _ left.val right.val)

theorem centralNormalizerCoefficientProjection_coeff {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) (subgroup intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (subgroup : Set G))
    (value : centralCoefficientSubring (G := G) ring) (element : intermediate) :
    (centralNormalizerCoefficientProjection ring subgroup intermediate hcontains hnormalizes value).val.coeff
      element = if element.val ∈ Subgroup.centralizer (subgroup : Set G) then
        value.val.coeff element.val else 0 :=
  normalizerCentralizerCoefficientProjection_coeff subgroup intermediate hcontains value.val element

theorem centralNormalizerCoefficientProjection_one {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) (subgroup intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (subgroup : Set G)) :
    centralNormalizerCoefficientProjection ring subgroup intermediate hcontains hnormalizes 1 = 1 := by
  apply Subtype.ext
  exact normalizerCentralizerCoefficientProjection_one subgroup intermediate hcontains

theorem centralNormalizerCoefficientProjection_scalar {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) (subgroup intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (subgroup : Set G)) (scalar : ring) :
    centralNormalizerCoefficientProjection ring subgroup intermediate hcontains hnormalizes
      (centralCoefficientScalarHom ring scalar) = centralCoefficientScalarHom ring scalar := by
  have hfirst := centralSubgroupCoefficientProjection_scalar ring
    (Subgroup.centralizer (subgroup : Set G)) scalar
  apply Subtype.ext
  change MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hcontains)
    (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set G))
      (MonoidAlgebra.single 1 scalar.val)) = MonoidAlgebra.single 1 scalar.val
  have hprojected := congrArg Subtype.val hfirst
  change subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set G))
    (MonoidAlgebra.single 1 scalar.val) = MonoidAlgebra.single 1 scalar.val at hprojected
  rw [hprojected, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, map_one]

theorem centralNormalizerCoefficientProjection_reduction {G : Type*}
    [Group G] [Fintype G] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (subgroup intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (subgroup : Set G))
    (value : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal)) :
    centralCoefficientReductionHom ideal
      (centralNormalizerCoefficientProjection (localizedComplexIntegerRing ideal)
        subgroup intermediate hcontains hnormalizes value) =
      normalizerCentralizerCoefficientProjection subgroup intermediate hcontains
        (centralCoefficientReductionHom ideal value) := by
  ext element
  simp only [centralCoefficientReductionHom, RingHom.comp_apply, MonoidAlgebra.coeff_mapRingHom,
    centralCoefficientLiftHom_coeff, centralNormalizerCoefficientProjection_coeff,
    normalizerCentralizerCoefficientProjection_coeff]
  split_ifs
  · rfl
  · exact map_zero _

theorem normalizerCentralizerCoefficientProjection_mul {ring G : Type*}
    [CommRing ring] [Group G] [Fintype G] (prime : ℕ) [Fact prime.Prime] [CharP ring prime]
    (subgroup : Subgroup G) (hgroup : IsPGroup prime subgroup) (intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (left right : MonoidAlgebra ring G)
    (hleft : subgroupConjugationInvariant subgroup left)
    (hright : subgroupConjugationInvariant subgroup right) :
    normalizerCentralizerCoefficientProjection subgroup intermediate hcontains (left * right) =
      normalizerCentralizerCoefficientProjection subgroup intermediate hcontains left *
        normalizerCentralizerCoefficientProjection subgroup intermediate hcontains right := by
  change MonoidAlgebra.mapDomainRingHom ring (Subgroup.inclusion hcontains)
    (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set G)) (left * right)) = _
  rw [prime_centralizer_coefficientProjection_mul prime subgroup hgroup left right hleft hright, map_mul]
  rfl

@[expose] noncomputable def brauerNormalizerCharacterResidueHom {G : Type*}
    [Group G] [Fintype G] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (subgroup : Subgroup G) (hgroup : IsPGroup prime subgroup) (intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (subgroup : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis intermediate) (label : localBasis.index) :
    centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal) →+*
      ComplexAlgebraicIntegers ⧸ ideal where
  toFun value := centralCharacterResidueHom localBasis ideal label
    (centralNormalizerCoefficientProjection (localizedComplexIntegerRing ideal)
      subgroup intermediate hcontains hnormalizes value)
  map_one' := by rw [centralNormalizerCoefficientProjection_one, map_one]
  map_zero' := by rw [map_zero, map_zero]
  map_add' left right := by rw [map_add, map_add]
  map_mul' left right := by
    let projection := centralNormalizerCoefficientProjection (localizedComplexIntegerRing ideal)
      subgroup intermediate hcontains hnormalizes
    have hzero : centralCoefficientReductionHom ideal
        (projection (left * right) - projection left * projection right) = 0 := by
      rw [(centralCoefficientReductionHom (G := intermediate) ideal).map_sub,
        (centralCoefficientReductionHom (G := intermediate) ideal).map_mul]
      change centralCoefficientReductionHom ideal
          (centralNormalizerCoefficientProjection _ subgroup intermediate hcontains hnormalizes (left * right)) -
        centralCoefficientReductionHom ideal
            (centralNormalizerCoefficientProjection _ subgroup intermediate hcontains hnormalizes left) *
          centralCoefficientReductionHom ideal
            (centralNormalizerCoefficientProjection _ subgroup intermediate hcontains hnormalizes right) = 0
      rw [centralNormalizerCoefficientProjection_reduction, centralNormalizerCoefficientProjection_reduction,
        centralNormalizerCoefficientProjection_reduction, map_mul,
        normalizerCentralizerCoefficientProjection_mul prime subgroup hgroup intermediate hcontains _ _
          (centralCoefficientReductionHom_conjugationInvariant ideal left subgroup)
          (centralCoefficientReductionHom_conjugationInvariant ideal right subgroup), sub_self]
    have hresidue := centralCharacterResidueHom_zero_of_coefficient_reduction_zero
      localBasis ideal _ hzero label
    rwa [(centralCharacterResidueHom localBasis ideal label).map_sub,
      (centralCharacterResidueHom localBasis ideal label).map_mul, sub_eq_zero] at hresidue

theorem brauerNormalizerCharacterResidueHom_scalar {G : Type*}
    [Group G] [Fintype G] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (subgroup : Subgroup G) (hgroup : IsPGroup prime subgroup) (intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (subgroup : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis intermediate) (label : localBasis.index) :
    (brauerNormalizerCharacterResidueHom ideal prime subgroup hgroup intermediate hcontains hnormalizes
      localBasis label).comp (centralCoefficientScalarHom (localizedComplexIntegerRing ideal)) =
      localizedComplexIntegerResidue ideal := by
  apply RingHom.ext
  intro scalar
  change centralCharacterResidueHom localBasis ideal label
    (centralNormalizerCoefficientProjection _ subgroup intermediate hcontains hnormalizes
      (centralCoefficientScalarHom _ scalar)) = _
  rw [centralNormalizerCoefficientProjection_scalar, centralCharacterResidueHom_scalar]

theorem brauerNormalizer_block_image_exists {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (subgroup : Subgroup G) (hgroup : IsPGroup prime subgroup) (intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (subgroup : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis intermediate) (localLabel : localBasis.index) :
    ∃ label : basis.index, brauerNormalizerCharacterResidueHom ideal prime subgroup hgroup intermediate
      hcontains hnormalizes localBasis localLabel = centralCharacterResidueHom basis ideal label := by
  exact centralCharacterResidueHom_completeness basis ideal _
    (brauerNormalizerCharacterResidueHom_scalar ideal prime subgroup hgroup intermediate hcontains
      hnormalizes localBasis localLabel)

end CFSG.TwoRankLowerBound.Helpers

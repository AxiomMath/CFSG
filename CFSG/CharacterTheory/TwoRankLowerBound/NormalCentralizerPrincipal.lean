module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPCentralResidueVanishing
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralSubalgebraResidueExtension
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCoefficientTransport

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

theorem normal_subgroup_centralizer_conjugation_mem {group : Type*} [Group group]
    (primary : Subgroup group) [primary.Normal] (conjugator element : group) :
    conjugator * element * conjugator⁻¹ ∈ Subgroup.centralizer (primary : Set group) ↔
      element ∈ Subgroup.centralizer (primary : Set group) :=
  centralizer_conjugation_mem_iff primary conjugator element
    ((Subgroup.normalizer_eq_top primary) ▸ Subgroup.mem_top conjugator)

noncomputable def normalCentralizerConjugationEquiv {group : Type*} [Group group]
    (primary : Subgroup group) [primary.Normal] (conjugator : group) :
    Subgroup.centralizer (primary : Set group) ≃* Subgroup.centralizer (primary : Set group) where
  toFun member := ⟨conjugator * member.val * conjugator⁻¹,
    (normal_subgroup_centralizer_conjugation_mem primary conjugator member.val).mpr member.property⟩
  invFun member := ⟨conjugator⁻¹ * member.val * conjugator,
    by simpa only [inv_inv] using
      (normal_subgroup_centralizer_conjugation_mem primary conjugator⁻¹ member.val).mpr member.property⟩
  left_inv member := Subtype.ext (by dsimp; group)
  right_inv member := Subtype.ext (by dsimp; group)
  map_mul' left right := Subtype.ext (by dsimp; group)

@[expose] noncomputable def commonCentralCoefficientSubring {group : Type*} [Group group]
    (ring : Subring ℂ) (subgroup : Subgroup group) :
    Subring (centralCoefficientSubring (G := subgroup) ring) :=
  (Subring.center (MonoidAlgebra ℂ group)).comap
    ((MonoidAlgebra.mapDomainRingHom ℂ subgroup.subtype).comp
      (centralCoefficientSubring (G := subgroup) ring).subtype)

@[expose] noncomputable def commonCentralCoefficientInclusion {group : Type*} [Group group]
    (ring : Subring ℂ) (subgroup : Subgroup group) :
    commonCentralCoefficientSubring ring subgroup →+* centralCoefficientSubring (G := group) ring where
  toFun value := ⟨MonoidAlgebra.mapDomainRingHom ℂ subgroup.subtype value.val.val, by
    constructor
    · intro element
      by_cases hmember : element ∈ subgroup
      · rw [show element = (⟨element, hmember⟩ : subgroup).val from rfl,
          groupAlgebra_subgroup_inclusion_coeff]
        exact centralCoefficientSubring_coefficients ring value.val _
      · rw [groupAlgebra_subgroup_inclusion_coeff_zero subgroup value.val.val element hmember]
        exact ring.zero_mem
    · exact value.property⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' left right := Subtype.ext (map_add _ left.val.val right.val.val)
  map_mul' left right := Subtype.ext (map_mul _ left.val.val right.val.val)

theorem commonCentralCoefficientScalar_mem {group : Type*} [Group group]
    (ring : Subring ℂ) (subgroup : Subgroup group) (scalar : ring) :
    centralCoefficientScalarHom (G := subgroup) ring scalar ∈ commonCentralCoefficientSubring ring subgroup := by
  change MonoidAlgebra.mapDomainRingHom ℂ subgroup.subtype
    (MonoidAlgebra.single 1 scalar.val) ∈ Subring.center (MonoidAlgebra ℂ group)
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, map_one]
  exact (centralCoefficientScalarHom (G := group) ring scalar).property.2

theorem commonCentralCoefficientInclusion_scalar {group : Type*} [Group group]
    (ring : Subring ℂ) (subgroup : Subgroup group) (scalar : ring) :
    commonCentralCoefficientInclusion ring subgroup
      ⟨centralCoefficientScalarHom ring scalar, commonCentralCoefficientScalar_mem ring subgroup scalar⟩ =
        centralCoefficientScalarHom ring scalar := by
  apply Subtype.ext
  change MonoidAlgebra.mapDomainRingHom ℂ subgroup.subtype (MonoidAlgebra.single 1 scalar.val) =
    MonoidAlgebra.single 1 scalar.val
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, map_one]

theorem commonCentralCoefficientInclusion_projection {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (subgroup : Subgroup group) (value : commonCentralCoefficientSubring ring subgroup) :
    centralSubgroupCoefficientProjection ring subgroup
      (commonCentralCoefficientInclusion ring subgroup value) = value.val :=
  Subtype.ext (subgroupCoefficientProjection_inclusion subgroup value.val.val)

theorem normalCentralizer_principal_idempotent_common {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (primary : Subgroup group) [primary.Normal]
    (basis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (primary : Set group)))
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    coefficientBlockIdempotent basis ring principal ∈
      commonCentralCoefficientSubring ring (Subgroup.centralizer (primary : Set group)) := by
  let centralizer := Subgroup.centralizer (primary : Set group)
  let idempotent := coefficientBlockIdempotent basis ring principal
  change MonoidAlgebra.mapDomainRingHom ℂ centralizer.subtype idempotent.val ∈
    Subring.center (MonoidAlgebra ℂ group)
  apply Subring.mem_center_iff.mpr
  intro other
  apply Commute.symm
  apply groupAlgebra_central_of_coeff_conjugation
  intro element conjugator
  by_cases hmember : element ∈ centralizer
  · let member : centralizer := ⟨element, hmember⟩
    let conjugated : centralizer := normalCentralizerConjugationEquiv primary conjugator member
    have hconjugated : conjugator * element * conjugator⁻¹ = conjugated.val := rfl
    rw [hconjugated, groupAlgebra_subgroup_inclusion_coeff, show element = member.val from rfl,
      groupAlgebra_subgroup_inclusion_coeff]
    have hequal := principal_block_idempotent_transport_fixed basis ring principal hprincipal
      (normalCentralizerConjugationEquiv primary conjugator)
    have hcoefficient := congrArg (fun value => value.val.coeff conjugated) hequal
    rw [centralCoefficientTransport_coeff] at hcoefficient
    change idempotent.val.coeff
      ((normalCentralizerConjugationEquiv primary conjugator).symm
        ((normalCentralizerConjugationEquiv primary conjugator) member)) = idempotent.val.coeff conjugated
      at hcoefficient
    rw [MulEquiv.symm_apply_apply] at hcoefficient
    exact hcoefficient.symm
  · have hconjugated : conjugator * element * conjugator⁻¹ ∉ centralizer := fun hinside =>
      hmember ((normal_subgroup_centralizer_conjugation_mem primary conjugator element).mp hinside)
    rw [groupAlgebra_subgroup_inclusion_coeff_zero centralizer idempotent.val _ hconjugated,
      groupAlgebra_subgroup_inclusion_coeff_zero centralizer idempotent.val _ hmember]

theorem normalCentralizer_projection_common {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (primary : Subgroup group) [primary.Normal]
    (value : centralCoefficientSubring (G := group) ring) :
    centralSubgroupCoefficientProjection ring (Subgroup.centralizer (primary : Set group)) value ∈
      commonCentralCoefficientSubring ring (Subgroup.centralizer (primary : Set group)) := by
  let centralizer := Subgroup.centralizer (primary : Set group)
  let projected := centralSubgroupCoefficientProjection ring centralizer value
  change MonoidAlgebra.mapDomainRingHom ℂ centralizer.subtype projected.val ∈
    Subring.center (MonoidAlgebra ℂ group)
  apply Subring.mem_center_iff.mpr
  intro other
  apply Commute.symm
  apply groupAlgebra_central_of_coeff_conjugation
  intro element conjugator
  by_cases hmember : element ∈ centralizer
  · have hconjugated := (normal_subgroup_centralizer_conjugation_mem primary conjugator element).mpr hmember
    change (MonoidAlgebra.mapDomainRingHom ℂ centralizer.subtype projected.val).coeff
      (⟨conjugator * element * conjugator⁻¹, hconjugated⟩ : centralizer).val =
        (MonoidAlgebra.mapDomainRingHom ℂ centralizer.subtype projected.val).coeff
          (⟨element, hmember⟩ : centralizer).val
    rw [groupAlgebra_subgroup_inclusion_coeff, groupAlgebra_subgroup_inclusion_coeff]
    change (subgroupCoefficientProjection centralizer value.val).coeff
      (⟨conjugator * element * conjugator⁻¹, hconjugated⟩ : centralizer) =
        (subgroupCoefficientProjection centralizer value.val).coeff (⟨element, hmember⟩ : centralizer)
    rw [subgroupCoefficientProjection_coeff, subgroupCoefficientProjection_coeff]
    exact central_groupAlgebra_coeff_conjugation value.val (centralCoefficientSubring_commutes ring value) _ _
  · have hconjugated : conjugator * element * conjugator⁻¹ ∉ centralizer := fun hinside =>
      hmember ((normal_subgroup_centralizer_conjugation_mem primary conjugator element).mp hinside)
    rw [groupAlgebra_subgroup_inclusion_coeff_zero centralizer projected.val _ hconjugated,
      groupAlgebra_subgroup_inclusion_coeff_zero centralizer projected.val _ hmember]

theorem commonCentralCoefficientInclusion_augmentation {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (subgroup : Subgroup group) (value : commonCentralCoefficientSubring ring subgroup) :
    groupAlgebraAugmentation ℂ group (commonCentralCoefficientInclusion ring subgroup value).val =
      groupAlgebraAugmentation ℂ subgroup value.val.val := by
  change groupAlgebraAugmentation ℂ group (MonoidAlgebra.mapDomainRingHom ℂ subgroup.subtype value.val.val) = _
  conv_lhs => rw [← groupAlgebra_sum_single value.val.val]
  simp only [map_sum, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
    groupAlgebraAugmentation_single]
  exact (groupAlgebraAugmentation_sum value.val.val).symm

theorem localCentralCharacterHom_included_principal_idempotent {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (primary : Subgroup group) [primary.Normal]
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (primary : Set group)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1) :
    centralCharacterResidueHom basis ideal principal
      (commonCentralCoefficientInclusion _ (Subgroup.centralizer (primary : Set group))
        ⟨coefficientBlockIdempotent localBasis _ localPrincipal,
          normalCentralizer_principal_idempotent_common _ primary localBasis localPrincipal hlocalPrincipal⟩) = 1 := by
  let included := commonCentralCoefficientInclusion (localizedComplexIntegerRing ideal)
    (Subgroup.centralizer (primary : Set group))
      ⟨coefficientBlockIdempotent localBasis _ localPrincipal,
        normalCentralizer_principal_idempotent_common _ primary localBasis localPrincipal hlocalPrincipal⟩
  have haugmentation : groupAlgebraAugmentation ℂ group included.val = 1 :=
    (commonCentralCoefficientInclusion_augmentation _ _ _).trans
      (principal_block_idempotent_augmentation localBasis _ localPrincipal hlocalPrincipal)
  have hscalar : localCentralCharacterHom basis ideal principal included = 1 := by
    apply Subtype.ext
    rw [localCentralCharacterHom_coe, centralCharacterScalar_principal basis principal hprincipal]
    exact haugmentation
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal principal included) = 1
  rw [hscalar, map_one]

theorem commonCentralCoefficientInclusion_injective {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (subgroup : Subgroup group) :
    Function.Injective (commonCentralCoefficientInclusion ring subgroup) := by
  intro left right hequal
  have hprojection := congrArg (centralSubgroupCoefficientProjection ring subgroup) hequal
  rw [commonCentralCoefficientInclusion_projection, commonCentralCoefficientInclusion_projection] at hprojection
  exact Subtype.ext hprojection

theorem centralSubalgebraResidue_extension_from_inclusion {source group : Type*}
    [CommRing source] [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (inclusion : source →+* centralCoefficientSubring (G := group) (localizedComplexIntegerRing ideal))
    (hinjective : Function.Injective inclusion)
    (scalar : localizedComplexIntegerRing ideal →+* source)
    (hscalarInclusion : ∀ value, inclusion (scalar value) = centralCoefficientScalarHom _ value)
    (hom : source →+* ComplexAlgebraicIntegers ⧸ ideal)
    (hscalarHom : ∀ value, hom (scalar value) = localizedComplexIntegerResidue ideal value) :
    ∃ label : basis.index, ∀ value, centralCharacterResidueHom basis ideal label (inclusion value) = hom value := by
  let equivalence := RingEquiv.ofBijective inclusion.rangeRestrict
    ⟨fun _ _ hequal => hinjective (congrArg Subtype.val hequal), inclusion.rangeRestrict_surjective⟩
  let rangeHom : inclusion.range →+* ComplexAlgebraicIntegers ⧸ ideal := hom.comp equivalence.symm.toRingHom
  have hcontains : ∀ value : localizedComplexIntegerRing ideal,
      centralCoefficientScalarHom _ value ∈ inclusion.range := fun value => ⟨scalar value, hscalarInclusion value⟩
  have hscalar : ∀ value, rangeHom ⟨centralCoefficientScalarHom _ value, hcontains value⟩ =
      localizedComplexIntegerResidue ideal value := by
    intro value
    have hequal : (⟨centralCoefficientScalarHom _ value, hcontains value⟩ : inclusion.range) =
        equivalence (scalar value) := Subtype.ext (hscalarInclusion value).symm
    change hom (equivalence.symm _) = _
    rw [hequal, equivalence.symm_apply_apply, hscalarHom]
  obtain ⟨label, hequal⟩ := centralSubalgebraResidue_extension basis ideal inclusion.range hcontains rangeHom hscalar
  refine ⟨label, ?_⟩
  intro value
  have hvalue := congrArg (fun result => result (equivalence value)) hequal
  change hom (equivalence.symm (equivalence value)) = centralCharacterResidueHom basis ideal label (inclusion value)
    at hvalue
  rw [equivalence.symm_apply_apply] at hvalue
  exact hvalue.symm

theorem commonCentralCoefficientScalarHom {group : Type*} [Group group]
    (ring : Subring ℂ) (subgroup : Subgroup group) :
    ∃ scalar : ring →+* commonCentralCoefficientSubring ring subgroup,
      ∀ value, scalar value = ⟨centralCoefficientScalarHom ring value,
        commonCentralCoefficientScalar_mem ring subgroup value⟩ := by
  exact ⟨(centralCoefficientScalarHom ring).codRestrict (commonCentralCoefficientSubring ring subgroup)
    (commonCentralCoefficientScalar_mem ring subgroup), fun _ => rfl⟩

theorem normalCentralizer_residue_restriction_exists {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (primary : Subgroup group)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (primary : Set group)))
    (label : basis.index) :
    ∃ localLabel : localBasis.index, ∀ value : commonCentralCoefficientSubring
      (localizedComplexIntegerRing ideal) (Subgroup.centralizer (primary : Set group)),
      centralCharacterResidueHom localBasis ideal localLabel value.val =
        centralCharacterResidueHom basis ideal label (commonCentralCoefficientInclusion _ _ value) := by
  let inclusion := commonCentralCoefficientInclusion (localizedComplexIntegerRing ideal)
    (Subgroup.centralizer (primary : Set group))
  obtain ⟨localLabel, hequal⟩ := centralSubalgebraResidue_extension localBasis ideal
    (commonCentralCoefficientSubring _ _) (commonCentralCoefficientScalar_mem _ _)
      ((centralCharacterResidueHom basis ideal label).comp inclusion) (by
        intro scalar
        change centralCharacterResidueHom basis ideal label (inclusion _) = _
        rw [commonCentralCoefficientInclusion_scalar, centralCharacterResidueHom_scalar])
  exact ⟨localLabel, fun value => (congrArg (fun hom => hom value) hequal).symm⟩

theorem normalCentralizer_residue_extension_exists {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (primary : Subgroup group)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (primary : Set group)))
    (localLabel : localBasis.index) :
    ∃ label : basis.index, ∀ value : commonCentralCoefficientSubring
      (localizedComplexIntegerRing ideal) (Subgroup.centralizer (primary : Set group)),
      centralCharacterResidueHom basis ideal label (commonCentralCoefficientInclusion _ _ value) =
        centralCharacterResidueHom localBasis ideal localLabel value.val := by
  obtain ⟨scalar, hscalar⟩ := commonCentralCoefficientScalarHom (localizedComplexIntegerRing ideal)
    (Subgroup.centralizer (primary : Set group))
  exact centralSubalgebraResidue_extension_from_inclusion basis ideal
    (commonCentralCoefficientInclusion _ _) (commonCentralCoefficientInclusion_injective _ _) scalar
    (fun value => by rw [hscalar, commonCentralCoefficientInclusion_scalar])
    ((centralCharacterResidueHom localBasis ideal localLabel).comp (commonCentralCoefficientSubring _ _).subtype)
    (fun value => by change centralCharacterResidueHom localBasis ideal localLabel (scalar value).val = _
                     rw [hscalar]; exact centralCharacterResidueHom_scalar localBasis ideal localLabel value)

theorem normalCentralizer_principal_detection {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) [primary.Normal] (hprimary : IsPGroup prime primary)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (primary : Set group)))
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (label : basis.index) (localLabel : localBasis.index)
    (hrestriction : ∀ value : commonCentralCoefficientSubring
      (localizedComplexIntegerRing ideal) (Subgroup.centralizer (primary : Set group)),
      centralCharacterResidueHom basis ideal label (commonCentralCoefficientInclusion _ _ value) =
        centralCharacterResidueHom localBasis ideal localLabel value.val) :
    centralCharacterResidueHom basis ideal label = centralCharacterResidueHom basis ideal principal ↔
      centralCharacterResidueHom localBasis ideal localLabel =
        centralCharacterResidueHom localBasis ideal localPrincipal := by
  constructor
  · intro hequal
    let idempotent : commonCentralCoefficientSubring (localizedComplexIntegerRing ideal)
      (Subgroup.centralizer (primary : Set group)) :=
      ⟨coefficientBlockIdempotent localBasis _ localPrincipal,
        normalCentralizer_principal_idempotent_common _ primary localBasis localPrincipal hlocalPrincipal⟩
    have hvalue := hrestriction idempotent
    rw [hequal, localCentralCharacterHom_included_principal_idempotent basis ideal principal hprincipal
      primary localBasis localPrincipal hlocalPrincipal] at hvalue
    have hmember : localLabel ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal := by
      have hresidue := centralCharacterResidueHom_block_idempotent localBasis ideal localPrincipal localLabel
      change centralCharacterResidueHom localBasis ideal localLabel idempotent.val = _ at hresidue
      rw [← hvalue] at hresidue
      by_contra hnot
      rw [ite_eq_right hnot] at hresidue
      exact one_ne_zero hresidue
    exact (sameCoefficientBlock_iff_centralCharacterResidueHom_eq localBasis ideal localLabel localPrincipal).mp
      (sameCoefficientBlock_symm localBasis _ ((coefficientBlock_mem_iff _ _ _ _).mp hmember))
  · intro hequal
    have hprincipalImage := brauerNormalizer_principal_residue_image basis ideal prime primary hprimary
      (Subgroup.centralizer (primary : Set group)) le_rfl (Subgroup.centralizer_le_normalizer _)
      localBasis principal hprincipal localPrincipal hlocalPrincipal
    apply RingHom.ext
    intro value
    let projected := centralSubgroupCoefficientProjection (localizedComplexIntegerRing ideal)
      (Subgroup.centralizer (primary : Set group)) value
    let common : commonCentralCoefficientSubring (localizedComplexIntegerRing ideal)
      (Subgroup.centralizer (primary : Set group)) :=
      ⟨projected, normalCentralizer_projection_common _ primary value⟩
    have hdetermined := normal_p_central_residue_determined_by_projection basis ideal prime primary hprimary
      value (commonCentralCoefficientInclusion _ _ common) (by
        rw [commonCentralCoefficientInclusion_projection]) label
    rw [hdetermined, hrestriction common, hequal]
    have himage := congrArg (fun hom => hom value) hprincipalImage
    change centralCharacterResidueHom localBasis ideal localPrincipal
      (centralNormalizerCoefficientProjection _ primary (Subgroup.centralizer (primary : Set group)) _ _ value) = _
      at himage
    have hprojection : centralNormalizerCoefficientProjection _ primary
        (Subgroup.centralizer (primary : Set group)) le_rfl (Subgroup.centralizer_le_normalizer _) value = projected := by
      apply Subtype.ext
      ext element
      rw [centralNormalizerCoefficientProjection_coeff, ite_eq_left element.property]
      exact (subgroupCoefficientProjection_coeff _ value.val element).symm
    rw [hprojection] at himage
    exact himage

end CFSG.TwoRankLowerBound.Helpers

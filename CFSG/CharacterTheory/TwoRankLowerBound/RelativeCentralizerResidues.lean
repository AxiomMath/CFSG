module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalCentralizerPrincipal

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def relativeCentralizerEquiv {group : Type*} [Group group]
    (primary intermediate : Subgroup group) (hprimary : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate) :
    Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate) ≃*
      Subgroup.centralizer (primary : Set group) where
  toFun member := ⟨member.val.val, by
    apply Subgroup.mem_centralizer_iff.mpr
    intro element helement
    have hequal := Subgroup.mem_centralizer_iff.mp member.property
      (⟨element, hprimary helement⟩ : intermediate) helement
    exact congrArg Subtype.val hequal⟩
  invFun member := ⟨⟨member.val, hcontains member.property⟩, by
    apply Subgroup.mem_centralizer_iff.mpr
    intro element helement
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp member.property element.val helement⟩
  left_inv member := rfl
  right_inv member := rfl
  map_mul' left right := rfl

theorem relativeCentralizerEquiv_apply {group : Type*} [Group group]
    (primary intermediate : Subgroup group) (hprimary : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (member : Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate)) :
    (relativeCentralizerEquiv primary intermediate hprimary hcontains member).val = member.val.val := rfl

@[expose] noncomputable def externalCommonCentralCoefficientSubring {group : Type*} [Group group]
    (ring : Subring ℂ) (primary intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate) :
    Subring (centralCoefficientSubring (G := Subgroup.centralizer (primary : Set group)) ring) :=
  (Subring.center (MonoidAlgebra ℂ intermediate)).comap
    ((MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hcontains)).comp
      (centralCoefficientSubring (G := Subgroup.centralizer (primary : Set group)) ring).subtype)

@[expose] noncomputable def externalCommonCentralCoefficientInclusion {group : Type*} [Group group]
    (ring : Subring ℂ) (primary intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate) :
    externalCommonCentralCoefficientSubring ring primary intermediate hcontains →+*
      centralCoefficientSubring (G := intermediate) ring where
  toFun value := ⟨MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hcontains) value.val.val, by
    constructor
    · intro element
      by_cases hmember : element.val ∈ Subgroup.centralizer (primary : Set group)
      · let member : Subgroup.centralizer (primary : Set group) := ⟨element.val, hmember⟩
        have hequal : Subgroup.inclusion hcontains member = element := Subtype.ext rfl
        rw [← hequal, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain,
          Finsupp.mapDomain_apply_of_injective (Subgroup.inclusion_injective hcontains)]
        exact centralCoefficientSubring_coefficients ring value.val member
      · rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
        have hzero : Finsupp.mapDomain (Subgroup.inclusion hcontains) value.val.val.coeff element = 0 := by
          apply Finsupp.mapDomain_of_notMem_range
          rintro ⟨member, hequal⟩
          exact hmember ((congrArg Subtype.val hequal) ▸ member.property)
        rw [hzero]
        exact ring.zero_mem
    · exact value.property⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' left right := Subtype.ext (map_add _ left.val.val right.val.val)
  map_mul' left right := Subtype.ext (map_mul _ left.val.val right.val.val)

theorem relativeCentralizer_groupAlgebra_inclusion {group : Type*} [Group group]
    (primary intermediate : Subgroup group) (hprimary : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (value : MonoidAlgebra ℂ (Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate))) :
    MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hcontains)
      (MonoidAlgebra.mapDomainRingHom ℂ
        (relativeCentralizerEquiv primary intermediate hprimary hcontains).toMonoidHom value) =
      MonoidAlgebra.mapDomainRingHom ℂ
        (Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate)).subtype value := by
  have hequal : (Subgroup.inclusion hcontains).comp
      (relativeCentralizerEquiv primary intermediate hprimary hcontains).toMonoidHom =
        (Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate)).subtype := by
    ext member
    rfl
  have hcomposition := congrArg (fun hom => hom value)
    (MonoidAlgebra.mapDomainRingHom_comp (R := ℂ) (Subgroup.inclusion hcontains)
      (relativeCentralizerEquiv primary intermediate hprimary hcontains).toMonoidHom)
  rw [hequal] at hcomposition
  exact hcomposition.symm

theorem externalCommonCentralCoefficient_mem_iff {group : Type*} [Group group]
    (ring : Subring ℂ) (primary intermediate : Subgroup group) (hprimary : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (value : centralCoefficientSubring (G :=
      Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate)) ring) :
    centralCoefficientTransport ring (relativeCentralizerEquiv primary intermediate hprimary hcontains) value ∈
      externalCommonCentralCoefficientSubring ring primary intermediate hcontains ↔
    value ∈ commonCentralCoefficientSubring ring
      (Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate)) := by
  change MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hcontains)
      (MonoidAlgebra.mapDomainRingHom ℂ
        (relativeCentralizerEquiv primary intermediate hprimary hcontains).toMonoidHom value.val) ∈
      Subring.center (MonoidAlgebra ℂ intermediate) ↔ _
  rw [relativeCentralizer_groupAlgebra_inclusion]
  rfl

set_option maxHeartbeats 4000000 in
@[expose] noncomputable def relativeCommonCentralCoefficientEquiv {group : Type*} [Group group]
    (ring : Subring ℂ) (primary intermediate : Subgroup group) (hprimary : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate) :
    commonCentralCoefficientSubring ring
      (Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate)) ≃+*
      externalCommonCentralCoefficientSubring ring primary intermediate hcontains where
  toFun value := ⟨centralCoefficientTransport ring
    (relativeCentralizerEquiv primary intermediate hprimary hcontains) value.val,
      (externalCommonCentralCoefficient_mem_iff ring primary intermediate hprimary hcontains value.val).mpr
        value.property⟩
  invFun value := ⟨centralCoefficientTransport ring
    (relativeCentralizerEquiv primary intermediate hprimary hcontains).symm value.val, by
      apply (externalCommonCentralCoefficient_mem_iff ring primary intermediate hprimary hcontains _).mp
      rw [show centralCoefficientTransport ring (relativeCentralizerEquiv primary intermediate hprimary hcontains)
        (centralCoefficientTransport ring (relativeCentralizerEquiv primary intermediate hprimary hcontains).symm
          value.val) = value.val from
        centralCoefficientTransport_inverse ring (relativeCentralizerEquiv primary intermediate hprimary hcontains).symm
          value.val]
      exact value.property⟩
  left_inv value := Subtype.ext (centralCoefficientTransport_inverse ring _ value.val)
  right_inv value := Subtype.ext (centralCoefficientTransport_inverse ring _ value.val)
  map_add' left right := Subtype.ext (map_add _ left.val right.val)
  map_mul' left right := Subtype.ext (map_mul _ left.val right.val)

theorem relativeCommonCentralCoefficientInclusion {group : Type*} [Group group]
    (ring : Subring ℂ) (primary intermediate : Subgroup group) (hprimary : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (value : commonCentralCoefficientSubring ring
      (Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate))) :
    externalCommonCentralCoefficientInclusion ring primary intermediate hcontains
      (relativeCommonCentralCoefficientEquiv ring primary intermediate hprimary hcontains value) =
        commonCentralCoefficientInclusion ring _ value :=
  Subtype.ext (relativeCentralizer_groupAlgebra_inclusion primary intermediate hprimary hcontains value.val.val)

theorem externalCommonCentralCoefficientInclusion_injective {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (primary intermediate : Subgroup group) (hprimary : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate) :
    Function.Injective (externalCommonCentralCoefficientInclusion ring primary intermediate hcontains) := by
  intro left right hequal
  let equivalence := relativeCommonCentralCoefficientEquiv ring primary intermediate hprimary hcontains
  have hequal' : commonCentralCoefficientInclusion ring _ (equivalence.symm left) =
      commonCentralCoefficientInclusion ring _ (equivalence.symm right) := by
    rw [← relativeCommonCentralCoefficientInclusion, ← relativeCommonCentralCoefficientInclusion]
    change externalCommonCentralCoefficientInclusion ring primary intermediate hcontains
        (equivalence (equivalence.symm left)) =
      externalCommonCentralCoefficientInclusion ring primary intermediate hcontains
        (equivalence (equivalence.symm right))
    rw [equivalence.apply_symm_apply, equivalence.apply_symm_apply]
    exact hequal
  exact equivalence.symm.injective (commonCentralCoefficientInclusion_injective ring _ hequal')

theorem externalCommonCentralCoefficientScalar_mem {group : Type*} [Group group]
    (ring : Subring ℂ) (primary intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate) (scalar : ring) :
    centralCoefficientScalarHom ring scalar ∈ externalCommonCentralCoefficientSubring ring primary intermediate hcontains := by
  change MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hcontains)
    (MonoidAlgebra.single 1 scalar.val) ∈ Subring.center (MonoidAlgebra ℂ intermediate)
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, map_one]
  exact (centralCoefficientScalarHom (G := intermediate) ring scalar).property.2

theorem externalCommonCentralCoefficientInclusion_scalar {group : Type*} [Group group]
    (ring : Subring ℂ) (primary intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate) (scalar : ring) :
    externalCommonCentralCoefficientInclusion ring primary intermediate hcontains
      ⟨centralCoefficientScalarHom ring scalar,
        externalCommonCentralCoefficientScalar_mem ring primary intermediate hcontains scalar⟩ =
          centralCoefficientScalarHom ring scalar := by
  apply Subtype.ext
  change MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hcontains) (MonoidAlgebra.single 1 scalar.val) =
    MonoidAlgebra.single 1 scalar.val
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, map_one]

theorem externalCommonCentralCoefficientProjection_mem {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (primary intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (value : centralCoefficientSubring (G := group) ring) :
    centralSubgroupCoefficientProjection ring (Subgroup.centralizer (primary : Set group)) value ∈
      externalCommonCentralCoefficientSubring ring primary intermediate hcontains :=
  (centralNormalizerCoefficientProjection ring primary intermediate hcontains hnormalizes value).property.2

theorem externalCommonCentralCoefficientProjection_inclusion {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (primary intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (value : centralCoefficientSubring (G := group) ring) :
    externalCommonCentralCoefficientInclusion ring primary intermediate hcontains
      ⟨centralSubgroupCoefficientProjection ring (Subgroup.centralizer (primary : Set group)) value,
        externalCommonCentralCoefficientProjection_mem ring primary intermediate hcontains hnormalizes value⟩ =
      centralNormalizerCoefficientProjection ring primary intermediate hcontains hnormalizes value := rfl

theorem externalCommonCentralizer_residue_extension_exists {group : Type*} [Group group] [Fintype group]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (primary intermediate : Subgroup group) (hprimary : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (intermediateBasis : FiniteIrreducibleCharacterBasis intermediate)
    (centralizerBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (primary : Set group)))
    (centralizerLabel : centralizerBasis.index) :
    ∃ label : intermediateBasis.index, ∀ value : externalCommonCentralCoefficientSubring
      (localizedComplexIntegerRing ideal) primary intermediate hcontains,
      centralCharacterResidueHom intermediateBasis ideal label
        (externalCommonCentralCoefficientInclusion _ primary intermediate hcontains value) =
          centralCharacterResidueHom centralizerBasis ideal centralizerLabel value.val := by
  let scalar := (centralCoefficientScalarHom (G := Subgroup.centralizer (primary : Set group))
    (localizedComplexIntegerRing ideal)).codRestrict (externalCommonCentralCoefficientSubring _ primary intermediate hcontains)
      (externalCommonCentralCoefficientScalar_mem _ primary intermediate hcontains)
  exact centralSubalgebraResidue_extension_from_inclusion intermediateBasis ideal
    (externalCommonCentralCoefficientInclusion _ primary intermediate hcontains)
    (externalCommonCentralCoefficientInclusion_injective _ primary intermediate hprimary hcontains) scalar
    (externalCommonCentralCoefficientInclusion_scalar _ primary intermediate hcontains)
    ((centralCharacterResidueHom centralizerBasis ideal centralizerLabel).comp
      (externalCommonCentralCoefficientSubring _ primary intermediate hcontains).subtype)
    (centralCharacterResidueHom_scalar centralizerBasis ideal centralizerLabel)

theorem externalCommonCentralizer_residue_restriction_exists {group : Type*} [Group group] [Fintype group]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (primary intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (intermediateBasis : FiniteIrreducibleCharacterBasis intermediate)
    (centralizerBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (primary : Set group)))
    (label : intermediateBasis.index) :
    ∃ centralizerLabel : centralizerBasis.index, ∀ value : externalCommonCentralCoefficientSubring
      (localizedComplexIntegerRing ideal) primary intermediate hcontains,
      centralCharacterResidueHom centralizerBasis ideal centralizerLabel value.val =
        centralCharacterResidueHom intermediateBasis ideal label
          (externalCommonCentralCoefficientInclusion _ primary intermediate hcontains value) := by
  obtain ⟨centralizerLabel, hequal⟩ := centralSubalgebraResidue_extension centralizerBasis ideal
    (externalCommonCentralCoefficientSubring _ primary intermediate hcontains)
    (externalCommonCentralCoefficientScalar_mem _ primary intermediate hcontains)
    ((centralCharacterResidueHom intermediateBasis ideal label).comp
      (externalCommonCentralCoefficientInclusion _ primary intermediate hcontains)) (by
        intro scalar
        rw [RingHom.comp_apply, externalCommonCentralCoefficientInclusion_scalar,
          centralCharacterResidueHom_scalar])
  exact ⟨centralizerLabel, fun value => (congrArg (fun hom => hom value) hequal).symm⟩

theorem externalCommonCentralizer_principal_detection {group : Type*} [Group group] [Fintype group]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary intermediate : Subgroup group) (hprimary : IsPGroup prime primary)
    (hprimaryContains : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (intermediateBasis : FiniteIrreducibleCharacterBasis intermediate)
    (centralizerBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (primary : Set group)))
    (principal : intermediateBasis.index) (hprincipal : (intermediateBasis.representation principal).character = 1)
    (centralizerPrincipal : centralizerBasis.index)
    (hcentralizerPrincipal : (centralizerBasis.representation centralizerPrincipal).character = 1)
    (label : intermediateBasis.index) (centralizerLabel : centralizerBasis.index)
    (hrestriction : ∀ value : externalCommonCentralCoefficientSubring
      (localizedComplexIntegerRing ideal) primary intermediate hcontains,
      centralCharacterResidueHom intermediateBasis ideal label
        (externalCommonCentralCoefficientInclusion _ primary intermediate hcontains value) =
          centralCharacterResidueHom centralizerBasis ideal centralizerLabel value.val) :
    centralCharacterResidueHom intermediateBasis ideal label =
        centralCharacterResidueHom intermediateBasis ideal principal ↔
      centralCharacterResidueHom centralizerBasis ideal centralizerLabel =
        centralCharacterResidueHom centralizerBasis ideal centralizerPrincipal := by
  let localPrimary := primary.subgroupOf intermediate
  let : localPrimary.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnormalizes
  let equivalence := relativeCentralizerEquiv primary intermediate hprimaryContains hcontains
  obtain ⟨internalBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (localPrimary : Set intermediate))
  obtain ⟨internalPrincipal, hinternalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible internalBasis
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hinternalPrincipal
  obtain ⟨internalLabel, htransport⟩ := centralCharacterResidueHom_transport_exists centralizerBasis internalBasis
    ideal equivalence.symm centralizerLabel
  have hrestriction' : ∀ value : commonCentralCoefficientSubring
      (localizedComplexIntegerRing ideal) (Subgroup.centralizer (localPrimary : Set intermediate)),
      centralCharacterResidueHom intermediateBasis ideal label (commonCentralCoefficientInclusion _ _ value) =
        centralCharacterResidueHom internalBasis ideal internalLabel value.val := by
    intro value
    have hresult := hrestriction
      (relativeCommonCentralCoefficientEquiv _ primary intermediate hprimaryContains hcontains value)
    rw [relativeCommonCentralCoefficientInclusion] at hresult
    have htransported := htransport (centralCoefficientTransport _ equivalence value.val)
    rw [centralCoefficientTransport_inverse] at htransported
    exact hresult.trans htransported.symm
  rw [normalCentralizer_principal_detection intermediateBasis ideal prime localPrimary hprimary.comap_subtype
    internalBasis principal hprincipal internalPrincipal hinternalPrincipal label internalLabel hrestriction']
  constructor
  · intro hequal
    apply RingHom.ext
    intro value
    rw [← htransport value, hequal]
    exact centralCharacterResidueHom_principal_transport centralizerBasis internalBasis ideal equivalence.symm
      centralizerPrincipal hcentralizerPrincipal internalPrincipal hinternalPrincipal value
  · intro hequal
    apply RingHom.ext
    intro value
    have htransported := htransport (centralCoefficientTransport _ equivalence value)
    rw [centralCoefficientTransport_inverse, hequal] at htransported
    exact htransported.trans (centralCharacterResidueHom_principal_transport internalBasis centralizerBasis ideal
      equivalence internalPrincipal hinternalPrincipal centralizerPrincipal hcentralizerPrincipal value)

theorem brauerNormalizer_principal_preimage_normalizer_replacement {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hprimaryContains : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (intermediateBasis : FiniteIrreducibleCharacterBasis intermediate)
    (principal : basis.index) (_hprincipal : (basis.representation principal).character = 1)
    (intermediatePrincipal : intermediateBasis.index)
    (hintermediatePrincipal : (intermediateBasis.representation intermediatePrincipal).character = 1)
    (label : intermediateBasis.index)
    (himage : brauerNormalizerCharacterResidueHom ideal prime primary hprimary intermediate hcontains hnormalizes
      intermediateBasis label = centralCharacterResidueHom basis ideal principal)
    (hnonprincipal : centralCharacterResidueHom intermediateBasis ideal label ≠
      centralCharacterResidueHom intermediateBasis ideal intermediatePrincipal) :
    ∃ (normalizerBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (primary : Set group)))
      (normalizerPrincipal normalizerLabel : normalizerBasis.index),
      (normalizerBasis.representation normalizerPrincipal).character = 1 ∧
      brauerNormalizerCharacterResidueHom ideal prime primary hprimary (Subgroup.normalizer (primary : Set group))
        (Subgroup.centralizer_le_normalizer _) le_rfl normalizerBasis normalizerLabel =
          centralCharacterResidueHom basis ideal principal ∧
      centralCharacterResidueHom normalizerBasis ideal normalizerLabel ≠
        centralCharacterResidueHom normalizerBasis ideal normalizerPrincipal := by
  let normalizer := Subgroup.normalizer (primary : Set group)
  obtain ⟨centralizerBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer (primary : Set group))
  obtain ⟨centralizerPrincipal, hcentralizerPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible centralizerBasis
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hcentralizerPrincipal
  obtain ⟨centralizerLabel, hrestriction⟩ := externalCommonCentralizer_residue_restriction_exists ideal
    primary intermediate hcontains intermediateBasis centralizerBasis label
  have hcentralizerNonprincipal : centralCharacterResidueHom centralizerBasis ideal centralizerLabel ≠
      centralCharacterResidueHom centralizerBasis ideal centralizerPrincipal := by
    intro hequal
    apply hnonprincipal
    exact (externalCommonCentralizer_principal_detection ideal prime primary intermediate hprimary hprimaryContains
      hcontains hnormalizes intermediateBasis centralizerBasis intermediatePrincipal hintermediatePrincipal
      centralizerPrincipal hcentralizerPrincipal label centralizerLabel (fun value => (hrestriction value).symm)).mpr hequal
  obtain ⟨normalizerBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := normalizer)
  obtain ⟨normalizerPrincipal, hnormalizerPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible normalizerBasis
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hnormalizerPrincipal
  obtain ⟨normalizerLabel, hextension⟩ := externalCommonCentralizer_residue_extension_exists ideal primary normalizer
    Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _) normalizerBasis centralizerBasis centralizerLabel
  refine ⟨normalizerBasis, normalizerPrincipal, normalizerLabel, hnormalizerPrincipal, ?_, ?_⟩
  · apply RingHom.ext
    intro value
    have hleft := hextension ⟨centralSubgroupCoefficientProjection _ (Subgroup.centralizer (primary : Set group)) value,
      externalCommonCentralCoefficientProjection_mem _ primary normalizer (Subgroup.centralizer_le_normalizer _) le_rfl value⟩
    have hright := hrestriction ⟨centralSubgroupCoefficientProjection _ (Subgroup.centralizer (primary : Set group)) value,
      externalCommonCentralCoefficientProjection_mem _ primary intermediate hcontains hnormalizes value⟩
    rw [externalCommonCentralCoefficientProjection_inclusion _ primary normalizer
      (Subgroup.centralizer_le_normalizer _) le_rfl value] at hleft
    rw [externalCommonCentralCoefficientProjection_inclusion _ primary intermediate hcontains hnormalizes value] at hright
    have hvalue := congrArg (fun hom => hom value) himage
    exact hleft.trans (hright.trans hvalue)
  · intro hequal
    apply hcentralizerNonprincipal
    exact (externalCommonCentralizer_principal_detection ideal prime primary normalizer hprimary Subgroup.le_normalizer
      (Subgroup.centralizer_le_normalizer _) le_rfl normalizerBasis centralizerBasis normalizerPrincipal
      hnormalizerPrincipal centralizerPrincipal hcentralizerPrincipal normalizerLabel centralizerLabel hextension).mp hequal

end CFSG.TwoRankLowerBound.Helpers

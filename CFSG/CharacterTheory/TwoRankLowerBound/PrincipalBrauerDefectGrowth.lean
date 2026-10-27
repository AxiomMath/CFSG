module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.CharacterTheory.TwoRankLowerBound.SylowPrincipalBrauer
public import CFSG.CharacterTheory.TwoRankLowerBound.LocalBlockExistence
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerProjectionTower

public section

open scoped Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

theorem normalizer_principal_preimage_defect_ne_primary {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary)
    (normalizerBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (primary : Set group)))
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (normalizerPrincipal label : normalizerBasis.index)
    (hnormalizerPrincipal : (normalizerBasis.representation normalizerPrincipal).character = 1)
    (himage : brauerNormalizerCharacterResidueHom ideal prime primary hprimary
      (Subgroup.normalizer (primary : Set group)) (Subgroup.centralizer_le_normalizer _) le_rfl
        normalizerBasis label = centralCharacterResidueHom basis ideal principal)
    (hnonprincipal : centralCharacterResidueHom normalizerBasis ideal label ≠
      centralCharacterResidueHom normalizerBasis ideal normalizerPrincipal)
    {defect : Subgroup (Subgroup.normalizer (primary : Set group))}
    (hdefect : coefficientBlockDefect normalizerBasis ideal prime label defect) :
    defect ≠ primary.subgroupOf (Subgroup.normalizer (primary : Set group)) := by
  intro hequal
  obtain ⟨conjugacyClass, hclass, hvalue⟩ := hdefect.1
  rw [hequal] at hclass
  obtain ⟨element, helement, hdefectAt⟩ := classDefect_normalizer_lift prime primary conjugacyClass hclass
  have hprojection := centralNormalizerCoefficientProjection_exact_defect_class prime
    (localizedComplexIntegerRing ideal) primary element hdefectAt
  have himageValue := congrArg (fun hom => hom (centralConjugacyClassSum
    (localizedComplexIntegerRing ideal) (ConjClasses.mk element.val))) himage
  change centralCharacterResidueHom normalizerBasis ideal label
    (centralNormalizerCoefficientProjection _ primary _ _ _ _) = _ at himageValue
  rw [hprojection, helement] at himageValue
  have hglobalValue : centralCharacterResidueHom basis ideal principal
      (centralConjugacyClassSum _ (ConjClasses.mk element.val)) ≠ 0 := by
    rwa [← himageValue]
  have hsylow := (principal_class_residue_ne_zero_iff_sylow basis ideal prime principal hprincipal
    (classDefectAt_classDefect hdefectAt)).mp hglobalValue
  apply hnonprincipal
  exact sylowNormalizer_principal_residue_preimage basis ideal prime primary hsylow normalizerBasis
    principal hprincipal normalizerPrincipal hnormalizerPrincipal label himage

theorem primary_centralizer_join_le_normalizer {group : Type*} [Group group]
    (primary : Subgroup group) :
    primary ⊔ Subgroup.centralizer (primary : Set group) ≤ Subgroup.normalizer (primary : Set group) :=
  sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)

theorem nested_primary_join_le_first_normalizer {group : Type*} [Group group]
    (primary larger : Subgroup group) (hprimary : primary ≤ larger)
    (hlarger : larger ≤ Subgroup.normalizer (primary : Set group)) :
    larger ⊔ Subgroup.centralizer (larger : Set group) ≤ Subgroup.normalizer (primary : Set group) :=
  sup_le hlarger ((Subgroup.centralizer_le hprimary).trans (Subgroup.centralizer_le_normalizer _))

theorem relativeCentralizer_le_join_subgroupOf {group : Type*} [Group group]
    (primary intermediate : Subgroup group) (hprimary : primary ≤ intermediate)
    (_hcentralizer : Subgroup.centralizer (primary : Set group) ≤ intermediate) :
    Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate) ≤
      (primary ⊔ Subgroup.centralizer (primary : Set group)).subgroupOf intermediate := by
  intro element hmember
  exact (show Subgroup.centralizer (primary : Set group) ≤ primary ⊔ Subgroup.centralizer (primary : Set group)
    from le_sup_right) ((relativeCentralizer_mem_iff primary intermediate hprimary element).mp hmember)

theorem relativeNormalizer_join_subgroupOf {group : Type*} [Group group]
    (primary intermediate : Subgroup group) (hprimary : primary ≤ intermediate) :
    (primary ⊔ Subgroup.centralizer (primary : Set group)).subgroupOf intermediate ≤
      Subgroup.normalizer (primary.subgroupOf intermediate : Set intermediate) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hprimary]
  exact Subgroup.comap_mono (primary_centralizer_join_le_normalizer primary)

theorem principal_residue_transport_reflect {group : Type*} [Group group] [Fintype group]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (intermediate smaller : Subgroup group) (hsmaller : smaller ≤ intermediate)
    (smallerBasis : FiniteIrreducibleCharacterBasis smaller)
    (internalBasis : FiniteIrreducibleCharacterBasis (smaller.subgroupOf intermediate))
    (smallerPrincipal : smallerBasis.index)
    (hsmallerPrincipal : (smallerBasis.representation smallerPrincipal).character = 1)
    (internalPrincipal : internalBasis.index)
    (hinternalPrincipal : (internalBasis.representation internalPrincipal).character = 1)
    (label : internalBasis.index) (smallerLabel : smallerBasis.index)
    (htransport : ∀ value, centralCharacterResidueHom smallerBasis ideal smallerLabel
      (centralCoefficientTransport _ (Subgroup.subgroupOfEquivOfLe hsmaller) value) =
        centralCharacterResidueHom internalBasis ideal label value)
    (hequal : centralCharacterResidueHom smallerBasis ideal smallerLabel =
      centralCharacterResidueHom smallerBasis ideal smallerPrincipal) :
    centralCharacterResidueHom internalBasis ideal label =
      centralCharacterResidueHom internalBasis ideal internalPrincipal := by
  apply RingHom.ext
  intro value
  rw [← htransport value, hequal]
  exact centralCharacterResidueHom_principal_transport internalBasis smallerBasis ideal
    (Subgroup.subgroupOfEquivOfLe hsmaller) internalPrincipal hinternalPrincipal
      smallerPrincipal hsmallerPrincipal value

theorem normalizer_principal_preimage_strict_growth {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary)
    (normalizerBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (primary : Set group)))
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (normalizerPrincipal label : normalizerBasis.index)
    (hnormalizerPrincipal : (normalizerBasis.representation normalizerPrincipal).character = 1)
    (himage : brauerNormalizerCharacterResidueHom ideal prime primary hprimary
      (Subgroup.normalizer (primary : Set group)) (Subgroup.centralizer_le_normalizer _) le_rfl
        normalizerBasis label = centralCharacterResidueHom basis ideal principal)
    (hnonprincipal : centralCharacterResidueHom normalizerBasis ideal label ≠
      centralCharacterResidueHom normalizerBasis ideal normalizerPrincipal) :
    ∃ (larger smaller : Subgroup group) (hlarger : IsPGroup prime larger)
      (_hprimaryContains : larger ≤ smaller)
      (hcontains : Subgroup.centralizer (larger : Set group) ≤ smaller)
      (hnormalizes : smaller ≤ Subgroup.normalizer (larger : Set group))
      (smallerBasis : FiniteIrreducibleCharacterBasis smaller)
      (smallerPrincipal smallerLabel : smallerBasis.index),
      Nat.card primary < Nat.card larger ∧
      (smallerBasis.representation smallerPrincipal).character = 1 ∧
      brauerNormalizerCharacterResidueHom ideal prime larger hlarger smaller hcontains hnormalizes
        smallerBasis smallerLabel = centralCharacterResidueHom basis ideal principal ∧
      centralCharacterResidueHom smallerBasis ideal smallerLabel ≠
        centralCharacterResidueHom smallerBasis ideal smallerPrincipal := by
  let normalizer := Subgroup.normalizer (primary : Set group)
  let localPrimary := primary.subgroupOf normalizer
  let : localPrimary.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨defect, hdefect⟩ := coefficientBlockDefect_exists normalizerBasis ideal prime label
  have hcontainsDefect : localPrimary ≤ defect :=
    normal_p_le_coefficientBlockDefect normalizerBasis ideal prime localPrimary hprimary.comap_subtype hdefect
  have hdefectNe : defect ≠ localPrimary := normalizer_principal_preimage_defect_ne_primary basis ideal prime
    primary hprimary normalizerBasis principal hprincipal normalizerPrincipal label hnormalizerPrincipal himage
      hnonprincipal hdefect
  let larger := defect.map normalizer.subtype
  have hlarger : IsPGroup prime larger := (coefficientBlockDefect_isPGroup normalizerBasis ideal hdefect).map _
  have hlargerContains : larger ≤ normalizer := Subgroup.map_subtype_le defect
  have hprimaryLarger : primary ≤ larger := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_normalizer (H := primary))]
    exact Subgroup.map_mono hcontainsDefect
  have hlocalLarger : larger.subgroupOf normalizer = defect :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective normalizer) defect
  have hstrict : Nat.card primary < Nat.card larger := by
    have hnotle : ¬Nat.card defect ≤ Nat.card localPrimary := by
      intro hcard
      exact hdefectNe (Subgroup.eq_of_le_of_card_ge hcontainsDefect hcard).symm
    have hcardPrimary : Nat.card localPrimary = Nat.card primary := by
      have hcard := Subgroup.card_map_of_injective (K := localPrimary) (Subgroup.subtype_injective normalizer)
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_normalizer (H := primary))] at hcard
      exact hcard.symm
    have hcardLarger : Nat.card larger = Nat.card defect :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective normalizer)
    rw [hcardLarger, ← hcardPrimary]
    exact Nat.lt_of_not_ge hnotle
  let smaller := larger ⊔ Subgroup.centralizer (larger : Set group)
  have hsmaller : smaller ≤ normalizer := nested_primary_join_le_first_normalizer primary larger
    hprimaryLarger hlargerContains
  have hcontains : Subgroup.centralizer (larger : Set group) ≤ smaller := le_sup_right
  have hnormalizes : smaller ≤ Subgroup.normalizer (larger : Set group) :=
    primary_centralizer_join_le_normalizer larger
  have hlocalContains : Subgroup.centralizer (larger.subgroupOf normalizer : Set normalizer) ≤
      smaller.subgroupOf normalizer :=
    relativeCentralizer_le_join_subgroupOf larger normalizer hlargerContains (hcontains.trans hsmaller)
  have hlocalNormalizes : smaller.subgroupOf normalizer ≤
      Subgroup.normalizer (larger.subgroupOf normalizer : Set normalizer) :=
    relativeNormalizer_join_subgroupOf larger normalizer hlargerContains
  obtain ⟨internalBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := smaller.subgroupOf normalizer)
  obtain ⟨internalPrincipal, hinternalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible internalBasis
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hinternalPrincipal
  obtain ⟨internalLabel, hlocalImage⟩ := brauerNormalizer_local_block_exists_of_subconjugate normalizerBasis ideal prime
    (larger.subgroupOf normalizer) hlarger.comap_subtype (smaller.subgroupOf normalizer)
      hlocalContains hlocalNormalizes internalBasis hdefect (by rw [hlocalLarger]; exact subgroupSubconjugate_refl defect)
  obtain ⟨smallerBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := smaller)
  obtain ⟨smallerPrincipal, hsmallerPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible smallerBasis
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hsmallerPrincipal
  obtain ⟨smallerLabel, htransport⟩ := centralCharacterResidueHom_transport_exists internalBasis smallerBasis ideal
    (Subgroup.subgroupOfEquivOfLe hsmaller) internalLabel
  refine ⟨larger, smaller, hlarger, le_sup_left, hcontains, hnormalizes, smallerBasis, smallerPrincipal,
    smallerLabel, hstrict, hsmallerPrincipal, ?_, ?_⟩
  · apply RingHom.ext
    intro value
    have htower := centralNormalizerCoefficientProjection_tower (localizedComplexIntegerRing ideal)
      primary larger normalizer smaller hprimaryLarger hlargerContains hsmaller
        (Subgroup.centralizer_le_normalizer _) le_rfl hcontains hnormalizes hlocalContains hlocalNormalizes value
    have hvalue := htransport (centralNormalizerCoefficientProjection _ (larger.subgroupOf normalizer)
      (smaller.subgroupOf normalizer) hlocalContains hlocalNormalizes
        (centralNormalizerCoefficientProjection _ primary normalizer (Subgroup.centralizer_le_normalizer _) le_rfl value))
    rw [htower] at hvalue
    have hlocalValue := congrArg (fun hom => hom
      (centralNormalizerCoefficientProjection _ primary normalizer (Subgroup.centralizer_le_normalizer _) le_rfl value))
        hlocalImage
    have himageValue := congrArg (fun hom => hom value) himage
    exact hvalue.trans (hlocalValue.trans himageValue)
  · intro hequal
    have hinternal := principal_residue_transport_reflect ideal normalizer smaller hsmaller smallerBasis internalBasis
      smallerPrincipal hsmallerPrincipal internalPrincipal hinternalPrincipal internalLabel smallerLabel htransport hequal
    have hprincipalImage := brauerNormalizer_principal_residue_image normalizerBasis ideal prime
      (larger.subgroupOf normalizer) hlarger.comap_subtype (smaller.subgroupOf normalizer) hlocalContains hlocalNormalizes
        internalBasis normalizerPrincipal hnormalizerPrincipal internalPrincipal hinternalPrincipal
    apply hnonprincipal
    apply RingHom.ext
    intro value
    have hlocalValue := congrArg (fun hom => hom value) hlocalImage
    have hprincipalValue := congrArg (fun hom => hom value) hprincipalImage
    change centralCharacterResidueHom internalBasis ideal internalLabel
      (centralNormalizerCoefficientProjection _ (larger.subgroupOf normalizer)
        (smaller.subgroupOf normalizer) hlocalContains hlocalNormalizes value) = _ at hlocalValue
    rw [hinternal] at hlocalValue
    exact hlocalValue.symm.trans hprincipalValue

end CFSG.TwoRankLowerBound.Helpers

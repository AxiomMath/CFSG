module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPBlockDefect
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalizerClassDefect

public section

open scoped Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

theorem centralNormalizerCoefficientProjection_exact_defect_class {group : Type*}
    [Group group] [Fintype group] (prime : ℕ) [Fact prime.Prime]
    (ring : Subring ℂ) (primary : Subgroup group)
    (element : Subgroup.normalizer (primary : Set group))
    (hdefect : classDefectAt prime primary element.val) :
    centralNormalizerCoefficientProjection ring primary (Subgroup.normalizer (primary : Set group))
      (Subgroup.centralizer_le_normalizer _) le_rfl
      (centralConjugacyClassSum ring (ConjClasses.mk element.val)) =
        centralConjugacyClassSum ring (ConjClasses.mk element) := by
  apply Subtype.ext
  ext other
  rw [centralNormalizerCoefficientProjection_coeff]
  change (if other.val ∈ Subgroup.centralizer (primary : Set group) then
      (conjugacyClassSum (ring := ℂ) (ConjClasses.mk element.val)).coeff other.val else 0) =
    (conjugacyClassSum (ring := ℂ) (ConjClasses.mk element)).coeff other
  rw [conjugacyClassSum_coeff, conjugacyClassSum_coeff]
  have hiff := exact_defect_class_intersection prime primary element other hdefect
  split_ifs <;> simp_all

set_option backward.isDefEq.respectTransparency false in
theorem classDefectAt_of_global_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary : Subgroup group)
    (hsylow : subgroupIsSylow prime primary) (element : group)
    (hcontains : primary ≤ Subgroup.centralizer ({element} : Set group)) :
    classDefectAt prime primary element := by
  obtain ⟨sylow, rfl⟩ := hsylow
  let centralizer := Subgroup.centralizer ({element} : Set group)
  have hrange : (sylow : Subgroup group) ≤ centralizer.subtype.range := by
    rwa [Subgroup.subtype_range]
  refine ⟨hcontains, sylow.comapOfInjective centralizer.subtype (Subgroup.subtype_injective _) hrange, ?_⟩
  rw [Sylow.coe_comapOfInjective]
  rfl

theorem normal_p_class_residue_zero_of_no_centralizer_member {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) [primary.Normal] (hprimary : IsPGroup prime primary)
    (conjugacyClass : ConjClasses group)
    (houtside : ¬∃ element : group, ConjClasses.mk element = conjugacyClass ∧
      element ∈ Subgroup.centralizer (primary : Set group)) (label : basis.index) :
    centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ conjugacyClass) = 0 := by
  obtain ⟨element, hclass⟩ := ConjClasses.exists_rep conjugacyClass
  rw [← hclass]
  apply normal_p_class_residue_zero basis ideal prime primary hprimary element _ label
  intro hmember
  exact houtside ⟨element, hclass, hmember⟩

theorem sylowNormalizer_principal_residue_preimage {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hsylow : subgroupIsSylow prime primary)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (primary : Set group)))
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (label : localBasis.index)
    (himage : brauerNormalizerCharacterResidueHom ideal prime primary
      ((subgroupIsSylow_iff prime primary).mp hsylow).1
      (Subgroup.normalizer (primary : Set group)) (Subgroup.centralizer_le_normalizer _) le_rfl
        localBasis label = centralCharacterResidueHom basis ideal principal) :
    centralCharacterResidueHom localBasis ideal label =
      centralCharacterResidueHom localBasis ideal localPrincipal := by
  let normalizer := Subgroup.normalizer (primary : Set group)
  let localPrimary := primary.subgroupOf normalizer
  let : localPrimary.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hprimary : IsPGroup prime primary := ((subgroupIsSylow_iff prime primary).mp hsylow).1
  have hprincipalImage := brauerNormalizer_principal_residue_image basis ideal prime primary hprimary
    normalizer (Subgroup.centralizer_le_normalizer _) le_rfl localBasis principal hprincipal
      localPrincipal hlocalPrincipal
  apply centralCharacterResidueHom_eq_of_class_values localBasis ideal label localPrincipal
  intro conjugacyClass
  obtain ⟨element, hclass⟩ := ConjClasses.exists_rep conjugacyClass
  rw [← hclass]
  by_cases hcentralizes : element.val ∈ Subgroup.centralizer (primary : Set group)
  · have hcontains : primary ≤ Subgroup.centralizer ({element.val} : Set group) := by
      intro member hmember
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hcentralizes member hmember)
    have hdefect := classDefectAt_of_global_sylow prime primary hsylow element.val hcontains
    have hprojection := centralNormalizerCoefficientProjection_exact_defect_class prime
      (localizedComplexIntegerRing ideal) primary element hdefect
    have hequal := congrArg (fun hom => hom (centralConjugacyClassSum
      (localizedComplexIntegerRing ideal) (ConjClasses.mk element.val)))
      (himage.trans hprincipalImage.symm)
    change centralCharacterResidueHom localBasis ideal label
        (centralNormalizerCoefficientProjection _ primary normalizer _ _ _) =
      centralCharacterResidueHom localBasis ideal localPrincipal
        (centralNormalizerCoefficientProjection _ primary normalizer _ _ _) at hequal
    rwa [hprojection] at hequal
  · have houtside : element ∉ Subgroup.centralizer (localPrimary : Set normalizer) := by
      intro hlocal
      apply hcentralizes
      apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      have hequal := Subgroup.mem_centralizer_iff.mp hlocal
        (⟨member, Subgroup.le_normalizer hmember⟩ : normalizer) hmember
      exact congrArg Subtype.val hequal
    rw [normal_p_class_residue_zero localBasis ideal prime localPrimary hprimary.comap_subtype
      element houtside label,
      normal_p_class_residue_zero localBasis ideal prime localPrimary hprimary.comap_subtype
        element houtside localPrincipal]

theorem sylowNormalizer_principal_block_preimage {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hsylow : subgroupIsSylow prime primary)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (primary : Set group)))
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (label : localBasis.index)
    (himage : brauerNormalizerCharacterResidueHom ideal prime primary
      ((subgroupIsSylow_iff prime primary).mp hsylow).1
      (Subgroup.normalizer (primary : Set group)) (Subgroup.centralizer_le_normalizer _) le_rfl
        localBasis label = centralCharacterResidueHom basis ideal principal) :
    sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) label localPrincipal :=
  (sameCoefficientBlock_iff_centralCharacterResidueHom_eq localBasis ideal label localPrincipal).mpr
    (sylowNormalizer_principal_residue_preimage basis ideal prime primary hsylow localBasis
      principal hprincipal localPrincipal hlocalPrincipal label himage)

end CFSG.TwoRankLowerBound.Helpers

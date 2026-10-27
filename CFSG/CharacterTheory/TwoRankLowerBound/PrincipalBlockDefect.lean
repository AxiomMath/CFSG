module

public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBrauerImage
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockDefectExistence

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

noncomputable def conjugacyClassSize {group : Type*} [Group group] [Finite group]
    (conjugacyClass : ConjClasses group) : ℕ := Nat.card conjugacyClass.carrier

set_option backward.isDefEq.respectTransparency false in
theorem conjugacyClassSize_centralizer_index {group : Type*} [Group group] [Fintype group]
    (element : group) :
    conjugacyClassSize (ConjClasses.mk element) = (Subgroup.centralizer ({element} : Set group)).index := by
  rw [Subgroup.centralizer_eq_comap_stabilizer,
    Subgroup.index_comap_of_surjective _ ConjAct.toConjAct.surjective,
    MulAction.index_stabilizer, ConjAct.orbit_eq_carrier_conjClasses]
  rfl

theorem centralCoefficientLiftHom_class_sum {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (conjugacyClass : ConjClasses group) :
    centralCoefficientLiftHom ring (centralConjugacyClassSum ring conjugacyClass) =
      conjugacyClassSum (ring := ring) conjugacyClass := by
  apply groupAlgebraCoefficientEmbedding_injective ring
  rw [centralCoefficientLiftHom_map]
  ext element
  change (conjugacyClassSum (ring := ℂ) conjugacyClass).coeff element =
    (MonoidAlgebra.mapRingHom group ring.subtype (conjugacyClassSum conjugacyClass)).coeff element
  simp only [MonoidAlgebra.coeff_mapRingHom, conjugacyClassSum_coeff]
  split_ifs <;> simp

theorem groupAlgebraAugmentation_class_sum {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (conjugacyClass : ConjClasses group) :
    groupAlgebraAugmentation ring group (conjugacyClassSum conjugacyClass) =
      (conjugacyClassSize conjugacyClass : ring) := by
  rw [groupAlgebraAugmentation_sum]
  simp only [conjugacyClassSum_coeff, Finset.sum_boole]
  rw [conjugacyClassSize, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [ConjClasses.mem_carrier_iff_mk_eq]

theorem centralCharacterResidueHom_principal_class_sum {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (conjugacyClass : ConjClasses group) :
    centralCharacterResidueHom basis ideal principal (centralConjugacyClassSum _ conjugacyClass) =
      (conjugacyClassSize conjugacyClass : ComplexAlgebraicIntegers ⧸ ideal) := by
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal principal _) = _
  rw [localCentralCharacterHom_principal basis ideal principal hprincipal,
    centralCoefficientLiftHom_class_sum, groupAlgebraAugmentation_class_sum, map_natCast]

@[expose] def subgroupIsSylow {group : Type*} [Group group] (prime : ℕ) (primary : Subgroup group) : Prop :=
  ∃ sylow : Sylow prime group, (sylow : Subgroup group) = primary

theorem subgroupIsSylow_iff {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary : Subgroup group) :
    subgroupIsSylow prime primary ↔ IsPGroup prime primary ∧ ¬prime ∣ primary.index := by
  constructor
  · rintro ⟨sylow, rfl⟩
    exact ⟨sylow.isPGroup', sylow.not_dvd_index⟩
  · rintro ⟨hprimary, hindex⟩
    exact ⟨hprimary.toSylow hindex, hprimary.toSylow_coe hindex⟩

theorem classDefect_sylow_iff_class_size {group : Type*} [Group group] [Fintype group]
    (prime : ℕ) [Fact prime.Prime] {conjugacyClass : ConjClasses group} {defect : Subgroup group}
    (hdefect : classDefect prime conjugacyClass defect) :
    subgroupIsSylow prime defect ↔ ¬prime ∣ conjugacyClassSize conjugacyClass := by
  obtain ⟨representative, hrepresentative, sylow, rfl⟩ := hdefect
  rw [subgroupIsSylow_iff, ← hrepresentative, conjugacyClassSize_centralizer_index,
    Subgroup.index_map_subtype]
  have hnotdivides := sylow.not_dvd_index
  have hgroup : IsPGroup prime
      ((sylow : Subgroup _).map (Subgroup.centralizer ({representative} : Set group)).subtype) :=
    sylow.isPGroup'.map _
  simp only [hgroup, true_and, (Fact.out : prime.Prime).dvd_mul, hnotdivides, false_or]

theorem principal_class_residue_ne_zero_iff_sylow {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {conjugacyClass : ConjClasses group} {defect : Subgroup group}
    (hdefect : classDefect prime conjugacyClass defect) :
    centralCharacterResidueHom basis ideal principal (centralConjugacyClassSum _ conjugacyClass) ≠ 0 ↔
      subgroupIsSylow prime defect := by
  rw [centralCharacterResidueHom_principal_class_sum basis ideal principal hprincipal,
    ne_eq, CharP.cast_eq_zero_iff, classDefect_sylow_iff_class_size prime hdefect]

set_option backward.isDefEq.respectTransparency false in
theorem classDefect_of_sylow_centralizes {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] {defect : Subgroup group}
    (hsylow : subgroupIsSylow prime defect) (element : group)
    (hcontains : defect ≤ Subgroup.centralizer ({element} : Set group)) :
    classDefect prime (ConjClasses.mk element) defect := by
  obtain ⟨sylow, rfl⟩ := hsylow
  let centralizer := Subgroup.centralizer ({element} : Set group)
  have hrange : (sylow : Subgroup group) ≤ centralizer.subtype.range := by
    rwa [Subgroup.subtype_range]
  let localSylow := sylow.comapOfInjective centralizer.subtype Subtype.val_injective hrange
  refine ⟨element, rfl, localSylow, ?_⟩
  change (sylow : Subgroup group) = (sylow.comapOfInjective centralizer.subtype
    Subtype.val_injective hrange : Subgroup centralizer).map centralizer.subtype
  rw [Sylow.coe_comapOfInjective]
  change (sylow : Subgroup group) = ((sylow : Subgroup group).subgroupOf centralizer).map centralizer.subtype
  exact (Subgroup.map_subgroupOf_eq_of_le hcontains).symm

theorem subgroupIsSylow_subconjugate {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] {left right : Subgroup group}
    (hleft : subgroupIsSylow prime left) (hright : subgroupIsSylow prime right) :
    subgroupSubconjugate left right := by
  obtain ⟨leftSylow, rfl⟩ := hleft
  obtain ⟨rightSylow, rfl⟩ := hright
  obtain ⟨conjugator, hconjugator⟩ := MulAction.exists_smul_eq group leftSylow rightSylow
  refine ⟨conjugator, ?_⟩
  intro element hmember
  rw [← hconjugator]
  change element ∈ MulAut.conj conjugator • (leftSylow : Subgroup group)
  exact hmember

theorem principal_coefficientBlockDefect_iff_sylow {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (defect : Subgroup group) :
    coefficientBlockDefect basis ideal prime principal defect ↔ subgroupIsSylow prime defect := by
  constructor
  · intro hdefect
    obtain ⟨_, hclass, hvalue⟩ := hdefect.1
    exact (principal_class_residue_ne_zero_iff_sylow basis ideal prime principal hprincipal hclass).mp hvalue
  · intro hsylow
    have hidentity : defect ≤ Subgroup.centralizer ({(1 : group)} : Set group) := by
      intro element _
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
    refine ⟨⟨ConjClasses.mk (1 : group), classDefect_of_sylow_centralizes prime hsylow 1 hidentity, ?_⟩, ?_⟩
    · rw [centralConjugacyClassSum_one, map_one]
      exact one_ne_zero
    · intro conjugacyClass other hclass hvalue
      exact subgroupIsSylow_subconjugate prime hsylow
        ((principal_class_residue_ne_zero_iff_sylow basis ideal prime principal hprincipal hclass).mp hvalue)

end CFSG.TwoRankLowerBound.Helpers

module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterConjugateInverse

public noncomputable section

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

universe u

theorem complete_character_basis_contains_irreducible {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (data : FiniteComplexRepresentation G)
    (hirreducible : data.IsIrreducible) :
    ∃! label : basis.index, (basis.representation label).character = data.character := by
  have hexists : ∃ label : basis.index, (basis.representation label).character = data.character := by
    by_contra! hnone
    have hzero : data.character = 0 := by
      apply basis.separates
      · exact Representation.char_conj data.representation
      · intro label
        rw [characterPairing_irreducible data (basis.representation label)
          hirreducible (basis.irreducible label), ite_eq_right (Ne.symm (hnone label))]
    exact irreducible_character_degree_ne_zero data hirreducible (congrFun hzero 1)
  obtain ⟨label, hlabel⟩ := hexists
  refine ⟨label, hlabel, ?_⟩
  intro other hother
  exact basis.distinct (hother.trans hlabel.symm)

@[expose] def IrreducibleComplexCharacter (G : Type u) [Group G] :=
  {character : G → ℂ // ∃ data : FiniteComplexRepresentation.{u, u} G,
    data.IsIrreducible ∧ data.character = character}

@[expose] def completeCharacterIndex {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) :
    basis.index → IrreducibleComplexCharacter G := fun label =>
  ⟨(basis.representation label).character, basis.representation label, basis.irreducible label, rfl⟩

theorem completeCharacterIndex_bijective {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) :
    Function.Bijective (completeCharacterIndex basis) := by
  constructor
  · intro left right heq
    exact basis.distinct (congrArg Subtype.val heq)
  · intro character
    obtain ⟨data, hirreducible, hdata⟩ := character.property
    obtain ⟨label, hlabel, _⟩ := complete_character_basis_contains_irreducible basis data hirreducible
    exact ⟨label, Subtype.ext (hlabel.trans hdata)⟩

@[expose] def completeCharacterEquiv {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) : basis.index ≃ IrreducibleComplexCharacter G :=
  Equiv.ofBijective (completeCharacterIndex basis) (completeCharacterIndex_bijective basis)

instance irreducibleComplexCharacter_finite {G : Type u} [Group G] [Finite G] :
    Finite (IrreducibleComplexCharacter G) := by
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  exact Finite.of_surjective (completeCharacterIndex basis)
    (completeCharacterIndex_bijective basis).surjective

noncomputable instance irreducibleComplexCharacter_fintype {G : Type u} [Group G] [Finite G] :
    Fintype (IrreducibleComplexCharacter G) := Fintype.ofFinite _

@[expose] def conjugatorCount {G : Type u} [Group G] [Fintype G]
    (selected element : G) : ℂ :=
  ∑ conjugator : G, if conjugator * selected * conjugator⁻¹ = element then 1 else 0

theorem conjugatorCount_conjugation {G : Type u} [Group G] [Fintype G]
    (selected element conjugator : G) :
    conjugatorCount selected (conjugator * element * conjugator⁻¹) =
      conjugatorCount selected element := by
  unfold conjugatorCount
  apply Fintype.sum_equiv (Equiv.mulLeft conjugator⁻¹)
  intro member
  change (if member * selected * member⁻¹ = conjugator * element * conjugator⁻¹ then 1 else 0) =
    if (conjugator⁻¹ * member) * selected * (conjugator⁻¹ * member)⁻¹ = element then 1 else 0
  have hiff : member * selected * member⁻¹ = conjugator * element * conjugator⁻¹ ↔
      (conjugator⁻¹ * member) * selected * (conjugator⁻¹ * member)⁻¹ = element := by
    constructor
    · intro h
      have hconj := congrArg (fun g : G => conjugator⁻¹ * g * conjugator) h
      convert hconj using 1 <;> group
    · intro h
      have hconj := congrArg (fun g : G => conjugator * g * conjugator⁻¹) h
      convert hconj using 1
      group
  simp only [hiff]

theorem conjugatorCount_pairing {G : Type u} [Group G] [Fintype G]
    (selected : G) (data : FiniteComplexRepresentation G) :
    characterPairing (conjugatorCount selected) data.character = data.character selected⁻¹ := by
  unfold characterPairing conjugatorCount
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  have hsum : ∀ conjugator : G,
      (∑ element : G, if conjugator * selected * conjugator⁻¹ = element then
        data.character element⁻¹ else 0) = data.character selected⁻¹ := by
    intro conjugator
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
    have hinv : (conjugator * selected * conjugator⁻¹)⁻¹ =
        conjugator * selected⁻¹ * conjugator⁻¹ := by group
    rw [hinv]
    exact Representation.char_conj data.representation selected⁻¹ conjugator
  simp only [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← mul_assoc]
  rw [inv_mul_cancel₀ (show (Nat.card G : ℂ) ≠ 0 from
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]

theorem conjugatorCount_self {G : Type u} [Group G] [Fintype G] (selected : G) :
    conjugatorCount selected selected = (Nat.card (Subgroup.centralizer {selected}) : ℂ) := by
  have hiff (member : G) : member * selected * member⁻¹ = selected ↔
      member ∈ Subgroup.centralizer {selected} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have heq := congrArg (fun g : G => g * member) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq
    · intro h
      rw [h]
      group
  simp only [conjugatorCount, hiff]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem complete_character_column_sum {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (selected element : G) :
    (∑ label, (basis.representation label).character selected⁻¹ *
      (basis.representation label).character element) = conjugatorCount selected element := by
  have h := finiteIrreducibleCharacterBasis_reconstruction basis (conjugatorCount selected)
    (conjugatorCount_conjugation selected) element
  simpa only [conjugatorCount_pairing] using h.symm

theorem complete_complex_character_column_sum {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (selected element : G) :
    (∑ label, (basis.representation label).character element *
      starRingEnd ℂ ((basis.representation label).character selected)) =
        conjugatorCount selected element := by
  simp only [finite_character_conjugate_inverse]
  calc
    (∑ label, (basis.representation label).character element *
        (basis.representation label).character selected⁻¹) =
      ∑ label, (basis.representation label).character selected⁻¹ *
        (basis.representation label).character element := by
          apply Finset.sum_congr rfl
          intro label _
          exact mul_comm _ _
    _ = conjugatorCount selected element := complete_character_column_sum basis selected element

theorem involution_character_is_real {G : Type u} [Group G] [Finite G]
    (data : FiniteComplexRepresentation G) (involution : G)
    (hsquare : involution ^ 2 = 1) :
    starRingEnd ℂ (data.character involution) = data.character involution := by
  have hinv : involution⁻¹ = involution :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hsquare)
  rw [finite_character_conjugate_inverse, hinv]

theorem complete_regular_character_sum {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (element : G) (hne : element ≠ 1) :
    (∑ label, (basis.representation label).character 1 *
      (basis.representation label).character element) = 0 := by
  have h := complete_character_column_sum basis 1 element
  simpa only [inv_one, conjugatorCount, mul_one, mul_inv_cancel, Ne.symm hne,
    ite_false, Finset.sum_const_zero] using h

theorem complete_involution_column_sum {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (involution : G)
    (hsquare : involution ^ 2 = 1) :
    (∑ label, (basis.representation label).character involution ^ 2) =
      (Nat.card (Subgroup.centralizer {involution}) : ℂ) := by
  have hinv : involution⁻¹ = involution := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hsquare)
  simpa only [hinv, ← pow_two, conjugatorCount_self] using
    complete_character_column_sum basis involution involution

theorem central_involution_character_ratio {G : Type u} [Group G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (involution : G) (hcentral : involution ∈ Subgroup.center G)
    (hsquare : involution ^ 2 = 1) :
    data.character involution / data.character 1 = 1 ∨
      data.character involution / data.character 1 = -1 := by
  obtain ⟨parity, hsign, hvalue, _⟩ :=
    irreducible_character_central_involution_parity data hirreducible involution hcentral hsquare
  have hratio : data.character involution / data.character 1 = parity := by
    exact (div_eq_iff (irreducible_character_degree_ne_zero data hirreducible)).mpr hvalue
  rwa [hratio]

theorem central_involution_weighted_summand {G : Type u} [Group G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (involution element : G) (hcentral : involution ∈ Subgroup.center G)
    (hsquare : involution ^ 2 = 1) (hconjugate : IsConj (involution * element) element)
    (scalar : ℂ) :
    (data.character involution / data.character 1) *
        (data.character involution + scalar * data.character element) ^ 2 =
      data.character 1 * data.character involution +
        2 * scalar * (data.character 1 * data.character element) +
        scalar ^ 2 * data.character element ^ 2 := by
  obtain ⟨parity, hsign, hvalue, htranslate⟩ :=
    irreducible_character_central_involution_parity data hirreducible involution hcentral hsquare
  have hratio : data.character involution / data.character 1 = parity := by
    exact (div_eq_iff (irreducible_character_degree_ne_zero data hirreducible)).mpr hvalue
  have hfixed : parity * data.character element = data.character element := by
    obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp hconjugate
    have hcharacters : data.character element = data.character (involution * element) := by
      have hchar := Representation.char_conj data.representation (involution * element) conjugator
      rw [hconjugator] at hchar
      exact hchar
    have hcommute := Subgroup.mem_center_iff.mp hcentral element
    have htranslateElement := htranslate element
    rw [hcommute] at htranslateElement
    exact htranslateElement.symm.trans hcharacters.symm
  rw [hratio, hvalue]
  rcases hsign with rfl | rfl
  · ring
  · have hzero : data.character element = 0 := by linear_combination -(1 / 2 : ℂ) * hfixed
    rw [hzero]
    ring

theorem central_involution_conjugate_product_weighted_character_sum
    {G : Type u} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (involution element : G) (hcentral : involution ∈ Subgroup.center G)
    (hinvolution : orderOf involution = 2) (helement : orderOf element = 2)
    (hconjugate : IsConj (involution * element) element) (scalar : ℂ) :
    (∀ label, (basis.representation label).character involution /
        (basis.representation label).character 1 = 1 ∨
      (basis.representation label).character involution /
        (basis.representation label).character 1 = -1) ∧
    (∑ label, ((basis.representation label).character involution /
          (basis.representation label).character 1) *
        ((basis.representation label).character involution +
          scalar * (basis.representation label).character element) ^ 2) =
      scalar ^ 2 * (Nat.card (Subgroup.centralizer {element}) : ℂ) := by
  have hsquare : involution ^ 2 = 1 := hinvolution ▸ pow_orderOf_eq_one involution
  have hesquare : element ^ 2 = 1 := helement ▸ pow_orderOf_eq_one element
  have hne : involution ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hinvolution
    omega
  have hene : element ≠ 1 := by
    intro h
    rw [h, orderOf_one] at helement
    omega
  refine ⟨fun label => central_involution_character_ratio (basis.representation label)
    (basis.irreducible label) involution hcentral hsquare, ?_⟩
  simp_rw [central_involution_weighted_summand _ (basis.irreducible _) involution element
    hcentral hsquare hconjugate scalar]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, complete_regular_character_sum basis involution hne,
    complete_regular_character_sum basis element hene,
    complete_involution_column_sum basis element hesquare]
  ring

theorem irreducible_central_involution_conjugate_product_weighted_sum
    {G : Type u} [Group G] [Finite G]
    (involution element : G) (hcentral : involution ∈ Subgroup.center G)
    (hinvolution : orderOf involution = 2) (helement : orderOf element = 2)
    (hconjugate : IsConj (involution * element) element) (scalar : ℂ) :
    (∀ character : IrreducibleComplexCharacter G,
      character.val involution / character.val 1 = 1 ∨
        character.val involution / character.val 1 = -1) ∧
    (∑ character : IrreducibleComplexCharacter G,
      (character.val involution / character.val 1) *
        (character.val involution + scalar * character.val element) ^ 2) =
      scalar ^ 2 * (Nat.card (Subgroup.centralizer {element}) : ℂ) := by
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨hsigns, hsum⟩ := central_involution_conjugate_product_weighted_character_sum basis
    involution element hcentral hinvolution helement hconjugate scalar
  constructor
  · intro character
    obtain ⟨label, rfl⟩ := (completeCharacterIndex_bijective basis).surjective character
    exact hsigns label
  · rw [← Equiv.sum_comp (completeCharacterEquiv basis)]
    exact hsum

end CFSG.Wreathed

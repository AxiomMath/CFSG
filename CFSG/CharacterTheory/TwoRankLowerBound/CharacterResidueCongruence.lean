module

public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicCharacterRing
public import CFSG.CharacterTheory.TwoRankLowerBound.PrimePrimaryFactorization

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def algebraicCharacterValue {G : Type*} [Group G] [Finite G]
    (data : FiniteComplexRepresentation G) (element : G) : ComplexAlgebraicIntegers :=
  ⟨data.character element, finite_character_value_isIntegral data element⟩

theorem irreducible_central_scalar_root {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (element : G) (hcentral : element ∈ Subgroup.center G) (exponent : ℕ)
    (hpositive : 0 < exponent) (hpower : element ^ exponent = 1) :
    ∃ scalar : ComplexAlgebraicIntegers, scalar ^ exponent = 1 ∧
      data.representation element = (scalar : ℂ) • (1 : Module.End ℂ data.vector) := by
  let : data.representation.IsIrreducible := hirreducible
  obtain ⟨scalar, hscalar⟩ := irreducible_central_element_is_scalar data.representation element hcentral
  let : Nontrivial data.representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) data.representation.asModule
  let : Nontrivial data.vector := data.representation.asModuleEquiv.symm.toEquiv.nontrivial
  have hroot : scalar ^ exponent = 1 := by
    apply smul_left_injective ℂ (show (1 : Module.End ℂ data.vector) ≠ 0 from one_ne_zero)
    calc
      scalar ^ exponent • (1 : Module.End ℂ data.vector) =
          (scalar • (1 : Module.End ℂ data.vector)) ^ exponent := by rw [smul_pow, one_pow]
      _ = data.representation element ^ exponent := by rw [hscalar]
      _ = 1 := by rw [← map_pow, hpower, map_one]
      _ = (1 : ℂ) • (1 : Module.End ℂ data.vector) := (one_smul _ _).symm
  refine ⟨⟨scalar, rootOfUnity_mem_complexAlgebraicIntegers scalar exponent hpositive hroot⟩, ?_, hscalar⟩
  apply Subtype.ext
  exact hroot

theorem irreducible_central_primary_character_congruence {G : Type*} [Group G] [Finite G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary regular : G) (hprimaryCentral : primary ∈ Subgroup.center G)
    (hregularCentral : regular ∈ Subgroup.center G) (exponent : ℕ)
    (hprimaryPower : primary ^ (prime ^ exponent) = 1) :
    algebraicCharacterValue data (primary * regular) - algebraicCharacterValue data regular ∈ ideal := by
  obtain ⟨primaryScalar, hprimaryRoot, hprimaryScalar⟩ := irreducible_central_scalar_root data hirreducible
    primary hprimaryCentral (prime ^ exponent) (pow_pos (Fact.out : Nat.Prime prime).pos _) hprimaryPower
  obtain ⟨regularScalar, _, hregularScalar⟩ := irreducible_central_scalar_root data hirreducible
    regular hregularCentral (orderOf regular) (orderOf_pos regular) (pow_orderOf_eq_one regular)
  have hrootMember : primaryScalar - 1 ∈ ideal :=
    prime_power_root_residue_one ideal prime primaryScalar exponent hprimaryRoot
  have hequal : algebraicCharacterValue data (primary * regular) - algebraicCharacterValue data regular =
      (regularScalar * (Module.finrank ℂ data.vector : ComplexAlgebraicIntegers)) * (primaryScalar - 1) := by
    apply Subtype.ext
    change data.character (primary * regular) - data.character regular =
      ((regularScalar : ℂ) * (Module.finrank ℂ data.vector : ℂ)) * ((primaryScalar : ℂ) - 1)
    change LinearMap.trace ℂ data.vector (data.representation (primary * regular)) -
      LinearMap.trace ℂ data.vector (data.representation regular) = _
    rw [map_mul, hprimaryScalar, hregularScalar, smul_mul_smul_comm, one_mul,
      map_smul, map_smul, LinearMap.trace_one]
    simp only [smul_eq_mul]
    ring
  rw [hequal]
  exact ideal.mul_mem_left _ hrootMember

theorem character_prime_primary_congruence {G : Type*} [Group G] [Finite G]
    (data : FiniteComplexRepresentation G) (element primary regular : G)
    (hprimary : primary ∈ Subgroup.zpowers element) (hregular : regular ∈ Subgroup.zpowers element)
    (hproduct : primary * regular = element)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (exponent : ℕ) (hprimaryPower : primary ^ (prime ^ exponent) = 1) :
    algebraicCharacterValue data element - algebraicCharacterValue data regular ∈ ideal := by
  let cyclic := Subgroup.zpowers element
  let : CommGroup cyclic := IsCyclic.commGroup
  let primaryElement : cyclic := ⟨primary, hprimary⟩
  let regularElement : cyclic := ⟨regular, hregular⟩
  let restricted := inflatedFiniteComplexRepresentation cyclic.subtype data
  obtain ⟨size, summand, hirreducible, hexpansion⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum restricted
  have hequal : algebraicCharacterValue data element - algebraicCharacterValue data regular =
      ∑ label : Fin size, (algebraicCharacterValue (summand label) (primaryElement * regularElement) -
        algebraicCharacterValue (summand label) regularElement) := by
    apply Subtype.ext
    change (integralClosure ℤ ℂ).val
      (algebraicCharacterValue data element - algebraicCharacterValue data regular) =
      (integralClosure ℤ ℂ).val (∑ label : Fin size,
        (algebraicCharacterValue (summand label) (primaryElement * regularElement) -
          algebraicCharacterValue (summand label) regularElement))
    simp only [map_sum, map_sub, Subalgebra.val_apply, algebraicCharacterValue]
    change data.character element - data.character regular =
      ∑ label : Fin size, ((summand label).character (primaryElement * regularElement) -
        (summand label).character regularElement)
    rw [Finset.sum_sub_distrib, ← hexpansion, ← hexpansion]
    change data.character element - data.character regular = data.character (primary * regular) - data.character regular
    rw [hproduct]
  rw [hequal]
  apply Submodule.sum_mem
  intro label _
  apply irreducible_central_primary_character_congruence (summand label) (hirreducible label) ideal prime
    primaryElement regularElement
  · rw [Subgroup.mem_center_iff]
    intro member
    exact mul_comm member primaryElement
  · rw [Subgroup.mem_center_iff]
    intro member
    exact mul_comm member regularElement
  · apply Subtype.ext
    exact hprimaryPower

theorem virtual_prime_primary_congruence {G : Type*} [Group G] [Finite G]
    (function : G → ℂ) (hvirtual : function ∈ virtualCharacters G) (element primary regular : G)
    (hprimary : primary ∈ Subgroup.zpowers element) (hregular : regular ∈ Subgroup.zpowers element)
    (hproduct : primary * regular = element)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (exponent : ℕ) (hprimaryPower : primary ^ (prime ^ exponent) = 1) :
    ∃ residue : ComplexAlgebraicIntegers, residue ∈ ideal ∧
      (residue : ℂ) = function element - function regular := by
  induction hvirtual using Submodule.span_induction with
  | mem character hmember =>
    obtain ⟨data, rfl⟩ := hmember
    exact ⟨algebraicCharacterValue data element - algebraicCharacterValue data regular,
      character_prime_primary_congruence data element primary regular hprimary hregular hproduct
        ideal prime exponent hprimaryPower, rfl⟩
  | zero => exact ⟨0, ideal.zero_mem, by simp⟩
  | add left right _ _ hleft hright =>
    obtain ⟨leftResidue, hleftMember, hleftValue⟩ := hleft
    obtain ⟨rightResidue, hrightMember, hrightValue⟩ := hright
    refine ⟨leftResidue + rightResidue, ideal.add_mem hleftMember hrightMember, ?_⟩
    change (leftResidue : ℂ) + rightResidue = _
    simp only [hleftValue, hrightValue, Pi.add_apply]
    ring
  | smul scalar function _ hfunction =>
    obtain ⟨residue, hmember, hvalue⟩ := hfunction
    refine ⟨(scalar : ComplexAlgebraicIntegers) * residue, ideal.mul_mem_left _ hmember, ?_⟩
    change (scalar : ℂ) * (residue : ℂ) = scalar • function element - scalar • function regular
    rw [hvalue, zsmul_eq_mul, zsmul_eq_mul]
    ring

theorem algebraicCharacterSpan_prime_primary_congruence {G : Type*} [Group G] [Finite G]
    (function : G → ℂ) (hmember : function ∈ algebraicCharacterSpan G) (element primary regular : G)
    (hprimary : primary ∈ Subgroup.zpowers element) (hregular : regular ∈ Subgroup.zpowers element)
    (hproduct : primary * regular = element)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (exponent : ℕ) (hprimaryPower : primary ^ (prime ^ exponent) = 1) :
    ∃ residue : ComplexAlgebraicIntegers, residue ∈ ideal ∧
      (residue : ℂ) = function element - function regular := by
  induction hmember using Submodule.span_induction with
  | mem character hvirtual =>
    exact virtual_prime_primary_congruence character hvirtual element primary regular hprimary hregular
      hproduct ideal prime exponent hprimaryPower
  | zero => exact ⟨0, ideal.zero_mem, by simp⟩
  | add left right _ _ hleft hright =>
    obtain ⟨leftResidue, hleftMember, hleftValue⟩ := hleft
    obtain ⟨rightResidue, hrightMember, hrightValue⟩ := hright
    refine ⟨leftResidue + rightResidue, ideal.add_mem hleftMember hrightMember, ?_⟩
    change (leftResidue : ℂ) + rightResidue = _
    simp only [hleftValue, hrightValue, Pi.add_apply]
    ring
  | smul scalar function _ hfunction =>
    obtain ⟨residue, hmember, hvalue⟩ := hfunction
    refine ⟨scalar * residue, ideal.mul_mem_left _ hmember, ?_⟩
    change (scalar : ℂ) * (residue : ℂ) = (scalar : ℂ) * function element - (scalar : ℂ) * function regular
    rw [hvalue]
    ring

theorem algebraicCharacterRing_prime_regular_evaluation {G : Type*} [Group G] [Finite G]
    (element : G) (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] :
    ∃ regular : G, regular ∈ Subgroup.zpowers element ∧ Nat.Coprime prime (orderOf regular) ∧
      ∀ function : algebraicCharacterRing G, (function : G → ComplexAlgebraicIntegers) element -
        (function : G → ComplexAlgebraicIntegers) regular ∈ ideal := by
  obtain ⟨primary, regular, exponent, hprimary, hregular, _, hproduct, hprimaryOrder, hregularOrder⟩ :=
    finite_prime_primary_factorization element prime Fact.out
  refine ⟨regular, hregular, hregularOrder, ?_⟩
  intro function
  obtain ⟨residue, hmember, hvalue⟩ := algebraicCharacterSpan_prime_primary_congruence
    (fun member => ((function : G → ComplexAlgebraicIntegers) member : ℂ)) function.property
    element primary regular hprimary hregular hproduct ideal prime exponent
    (orderOf_dvd_iff_pow_eq_one.mp hprimaryOrder)
  have hequal : (function : G → ComplexAlgebraicIntegers) element -
      (function : G → ComplexAlgebraicIntegers) regular = residue := by
    apply Subtype.ext
    exact hvalue.symm
  rw [hequal]
  exact hmember

end CFSG.TwoRankLowerBound.Helpers

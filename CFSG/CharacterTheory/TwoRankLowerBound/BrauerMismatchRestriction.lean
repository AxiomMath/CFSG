module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerMismatchTrace
public import CFSG.CharacterTheory.TwoRankLowerBound.BimoduleCharacterTrace
public import CFSG.CharacterTheory.TwoRankLowerBound.BimoduleCoefficientExtension

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem complex_local_subgroupBimodule_mismatch_trace_zero {group : Type*}
    [Group group] [Fintype group] (ring : Subring ℂ) [IsLocalRing ring]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (primary : group) (exponent : ℕ) (hprimary : orderOf primary ∣ prime ^ exponent)
    (regular : Subgroup.centralizer (Subgroup.zpowers primary : Set group))
    (hregular : Nat.Coprime prime (orderOf regular.val))
    (hroots : ∀ period : ℕ, 0 < period → ∀ root : ℂ, root ^ period = 1 → root ∈ ring)
    (left : MonoidAlgebra ring group)
    (right : MonoidAlgebra ring (Subgroup.centralizer (Subgroup.zpowers primary : Set group)))
    (hleft : ∀ element : group, Commute left (MonoidAlgebra.single element 1))
    (hright : ∀ element : Subgroup.centralizer (Subgroup.zpowers primary : Set group),
      Commute right (MonoidAlgebra.single element 1))
    (hleftIdempotent : IsIdempotentElem left) (hrightIdempotent : IsIdempotentElem right)
    (hzero : MonoidAlgebra.mapRingHom (Subgroup.centralizer (Subgroup.zpowers primary : Set group))
      (IsLocalRing.residue ring)
      (subgroupCoefficientProjection (Subgroup.centralizer (Subgroup.zpowers primary : Set group)) left * right) = 0)
    (element : group) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ group)
      (subgroupBimoduleProjection (Subgroup.centralizer (Subgroup.zpowers primary : Set group))
          (MonoidAlgebra.mapRingHom group ring.subtype left)
          (MonoidAlgebra.mapRingHom (Subgroup.centralizer (Subgroup.zpowers primary : Set group)) ring.subtype right) *
        Representation.ofMulAction ℂ (Equiv.Perm group) group
          (groupTwoSidedPermutationHom group (element, primary * regular.val))) = 0 := by
  obtain ⟨leftPrimary, leftRegular, leftExponent, _, _, hparts, hproduct, hleftPrimary, hleftRegular⟩ :=
    finite_prime_primary_factorization element prime Fact.out
  let period := orderOf leftRegular * orderOf regular.val
  have hpositive : 0 < period := Nat.mul_pos (orderOf_pos leftRegular) (orderOf_pos regular.val)
  have hcoprime : ¬ prime ∣ period :=
    (Fact.out : prime.Prime).coprime_iff_not_dvd.mp (hleftRegular.mul_right hregular)
  have hperiodUnit := local_residue_prime_complement_unit prime period hcoprime (ring := ring)
  obtain ⟨root, hroot⟩ := complex_subring_primitiveRoot_unit ring period hpositive (hroots period hpositive)
  have hleftPeriod : leftRegular ^ period = 1 := by
    change leftRegular ^ (orderOf leftRegular * orderOf regular.val) = 1
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have hrightPeriod : regular.val ^ period = 1 := by
    change regular.val ^ (orderOf leftRegular * orderOf regular.val) = 1
    rw [pow_mul', pow_orderOf_eq_one, one_pow]
  have htrace := subgroupBimodule_mismatch_section_trace_zero prime primary leftPrimary leftRegular regular
    leftExponent exponent hleftPrimary hprimary hparts period hperiodUnit.unit root hperiodUnit.unit_spec hroot
    hleftPeriod hrightPeriod left right hleft hright hleftIdempotent hrightIdempotent hzero
  rw [hproduct] at htrace
  rw [← permutationCoefficientExtension_subgroupBimodule ring,
    ← permutationCoefficientExtension_translation ring.subtype, ← map_mul,
    permutationCoefficientExtension_trace, htrace, map_zero]

theorem lifted_characterSubsetIdempotent_central {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ) (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis ring support) :
    ∀ other, Commute (liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support) hadmissible) other := by
  intro other
  apply groupAlgebraCoefficientEmbedding_injective ring
  rw [map_mul, map_mul, liftGroupAlgebraCoefficients_map ring (characterSubsetIdempotent basis support) hadmissible]
  exact (characterIdempotentExpansion_central basis _ _).eq

theorem lifted_characterSubsetIdempotent_idempotent {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ) (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis ring support) :
    IsIdempotentElem (liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support) hadmissible) := by
  change liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support) hadmissible *
    liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support) hadmissible = _
  apply groupAlgebraCoefficientEmbedding_injective ring
  rw [map_mul, liftGroupAlgebraCoefficients_map ring (characterSubsetIdempotent basis support) hadmissible]
  exact (characterSubsetIdempotent_isIdempotent basis support).eq

theorem admissible_mismatch_character_local_projection_zero {group : Type*}
    [Group group] [Fintype group] (ring : Subring ℂ) [IsLocalRing ring]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis ring support)
    (primary : group) (exponent : ℕ) (hprimary : orderOf primary ∣ prime ^ exponent)
    (localBasis : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers primary : Set group)))
    (localSupport : Finset localBasis.index)
    (hlocalAdmissible : characterSubsetAdmissible localBasis ring localSupport)
    (regular : Subgroup.centralizer (Subgroup.zpowers primary : Set group))
    (hregular : Nat.Coprime prime (orderOf regular.val))
    (hroots : ∀ period : ℕ, 0 < period → ∀ root : ℂ, root ^ period = 1 → root ∈ ring)
    (hzero : MonoidAlgebra.mapRingHom (Subgroup.centralizer (Subgroup.zpowers primary : Set group))
      (IsLocalRing.residue ring)
      (subgroupCoefficientProjection (Subgroup.centralizer (Subgroup.zpowers primary : Set group))
          (liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support) hadmissible) *
        liftGroupAlgebraCoefficients ring (characterSubsetIdempotent localBasis localSupport) hlocalAdmissible) = 0)
    (label : basis.index) (hlabel : label ∈ support) :
    characterSubsetProjection localBasis localSupport
      (fun member => (basis.representation label).character member.val)
      ((⟨primary, element_mem_centralizer_zpowers primary⟩ :
        Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹ = 0 := by
  let rightElement : Subgroup.centralizer (Subgroup.zpowers primary : Set group) :=
    ⟨primary, element_mem_centralizer_zpowers primary⟩ * regular
  let coefficient : basis.index → ℂ := fun member => if member ∈ support then
    characterSubsetProjection localBasis localSupport
      (fun element => (basis.representation member).character element.val) rightElement⁻¹ else 0
  have hsum : ∀ element : group, ∑ member, coefficient member * (basis.representation member).character element = 0 := by
    intro element
    have htrace := complex_local_subgroupBimodule_mismatch_trace_zero ring prime primary exponent hprimary regular
      hregular hroots
      (liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support) hadmissible)
      (liftGroupAlgebraCoefficients ring (characterSubsetIdempotent localBasis localSupport) hlocalAdmissible)
      (fun member => lifted_characterSubsetIdempotent_central basis ring support hadmissible _)
      (fun member => lifted_characterSubsetIdempotent_central localBasis ring localSupport hlocalAdmissible _)
      (lifted_characterSubsetIdempotent_idempotent basis ring support hadmissible)
      (lifted_characterSubsetIdempotent_idempotent localBasis ring localSupport hlocalAdmissible) hzero element
    rw [liftGroupAlgebraCoefficients_map ring (characterSubsetIdempotent basis support) hadmissible,
      liftGroupAlgebraCoefficients_map ring (characterSubsetIdempotent localBasis localSupport) hlocalAdmissible] at htrace
    change LinearMap.trace ℂ (MonoidAlgebra ℂ group)
      (subgroupBimoduleProjection _ (characterSubsetIdempotent basis support)
        (characterSubsetIdempotent localBasis localSupport) *
          Representation.ofMulAction ℂ (Equiv.Perm group) group
            (groupTwoSidedPermutationHom group (element, rightElement.val))) = 0 at htrace
    rw [characterSubsetBimodule_local_projection_trace] at htrace
    simp only [coefficient, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem_eq]
    simpa only [mul_comm] using htrace
  have hfunction : (fun element : group => ∑ member,
      coefficient member * (basis.representation member).character element) = 0 := funext hsum
  have hpairing := characterPairing_distinct_expansion_coefficient basis.representation basis.irreducible
    basis.distinct coefficient label
  rw [hfunction] at hpairing
  have hcoefficient : coefficient label = 0 := by
    simpa only [characterPairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero] using hpairing.symm
  simpa only [coefficient, ite_eq_left hlabel] using hcoefficient

end CFSG.TwoRankLowerBound.Helpers

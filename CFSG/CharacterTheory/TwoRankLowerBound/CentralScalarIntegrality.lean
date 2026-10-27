module

public import CFSG.CharacterTheory.TwoRankLowerBound.LocalizedAlgebraicIntegers
public import CFSG.CharacterTheory.TwoRankLowerBound.CoefficientBlocks

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupAlgebraCoefficientSubring_exists_preimage {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) (algebraElement : MonoidAlgebra ℂ G)
    (hcoefficients : algebraElement ∈ groupAlgebraCoefficientSubring ring) :
    ∃ preimage : MonoidAlgebra ring G,
      MonoidAlgebra.mapRingHom G ring.subtype preimage = algebraElement := by
  refine ⟨∑ element : G, MonoidAlgebra.single element
    ⟨algebraElement.coeff element, hcoefficients element⟩, ?_⟩
  ext element
  simp only [map_sum, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_single]
  simp

theorem irreducible_scalar_action_isIntegral {G : Type*} [Group G] [Fintype G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (ring : Subring ℂ) (algebraElement : MonoidAlgebra ℂ G)
    (hcoefficients : algebraElement ∈ groupAlgebraCoefficientSubring ring)
    (scalar : ℂ)
    (haction : data.representation.asAlgebraHom algebraElement =
      scalar • (1 : Module.End ℂ data.vector)) : IsIntegral ring scalar := by
  let ringAlgebra : Algebra ring (Module.End ℂ data.vector) :=
    Algebra.compHom (Module.End ℂ data.vector) ring.subtype
  let tower : IsScalarTower ring ℂ (Module.End ℂ data.vector) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨preimage, hpreimage⟩ :=
    groupAlgebraCoefficientSubring_exists_preimage ring algebraElement hcoefficients
  let action : MonoidAlgebra ring G →+* Module.End ℂ data.vector :=
    data.representation.asAlgebraHom.toRingHom.comp (MonoidAlgebra.mapRingHom G ring.subtype)
  have hcompatible : (algebraMap ring (Module.End ℂ data.vector)).comp (RingHom.id ring) =
      action.comp (algebraMap ring (MonoidAlgebra ring G)) := by
    apply RingHom.ext
    intro coefficient
    change (algebraMap ℂ (Module.End ℂ data.vector)) (coefficient : ℂ) =
      data.representation.asAlgebraHom
        (MonoidAlgebra.mapRingHom G ring.subtype (MonoidAlgebra.single 1 coefficient))
    rw [MonoidAlgebra.mapRingHom_single, Representation.asAlgebraHom_single, map_one]
    exact Algebra.algebraMap_eq_smul_one _
  have hintegral : IsIntegral ring (action preimage) :=
    IsIntegral.map_of_comp_eq (RingHom.id ring) action hcompatible
      (IsIntegral.of_finite ring preimage)
  change IsIntegral ring (data.representation.asAlgebraHom
    (MonoidAlgebra.mapRingHom G ring.subtype preimage)) at hintegral
  rw [hpreimage, haction] at hintegral
  have hinjective : Function.Injective (algebraMap ℂ (Module.End ℂ data.vector)) := by
    simpa only [Algebra.algebraMap_eq_smul_one'] using
      irreducible_scalar_identity_injective data hirreducible
  apply (@isIntegral_algebraMap_iff ring ℂ (Module.End ℂ data.vector)
    _ _ _ _ ringAlgebra _ tower scalar
      ((faithfulSMul_iff_algebraMap_injective ℂ (Module.End ℂ data.vector)).mpr hinjective)).mp
  simpa only [Algebra.algebraMap_eq_smul_one] using hintegral

theorem centralCharacterScalar_isIntegral {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ring : Subring ℂ)
    (algebraElement : MonoidAlgebra ℂ G)
    (hcoefficients : algebraElement ∈ groupAlgebraCoefficientSubring ring)
    (hcentral : ∀ other : MonoidAlgebra ℂ G, Commute algebraElement other)
    (label : basis.index) : IsIntegral ring (centralCharacterScalar basis algebraElement label) := by
  exact irreducible_scalar_action_isIntegral (basis.representation label) (basis.irreducible label)
    ring algebraElement hcoefficients _
    (centralCharacterScalar_action basis algebraElement hcentral label)

theorem localizedComplexIntegerRing_integral_mem
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] (value : ℂ)
    (hintegral : IsIntegral (localizedComplexIntegerRing ideal) value) :
    value ∈ localizedComplexIntegerRing ideal := by
  let : Algebra (Localization.AtPrime ideal) ℂ :=
    (localizedAlgebraicIntegerEmbedding ideal).toAlgebra
  let : IsScalarTower ComplexAlgebraicIntegers (Localization.AtPrime ideal) ℂ :=
    IsScalarTower.of_algebraMap_eq fun integer =>
      (localizedAlgebraicIntegerEmbedding_constant ideal integer).symm
  have hlocalizedIntegral : IsIntegral (Localization.AtPrime ideal) value := by
    apply IsIntegral.map_of_comp_eq
      (localizedComplexIntegerEquiv ideal).symm.toRingHom (RingHom.id ℂ) _ hintegral
    ext coefficient
    change localizedAlgebraicIntegerEmbedding ideal
      ((localizedComplexIntegerEquiv ideal).symm coefficient) = coefficient.val
    have hequal := congrArg Subtype.val
      ((localizedComplexIntegerEquiv ideal).apply_symm_apply coefficient)
    exact hequal
  obtain ⟨denominator, hmultiple⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization ideal.primeCompl value hlocalizedIntegral
  let : Algebra.IsIntegral ℤ ComplexAlgebraicIntegers := complexAlgebraicIntegers_integral
  have hproduct : IsIntegral ℤ ((denominator.val.val : ℂ) * value) := by
    exact isIntegral_trans _ hmultiple
  refine (localizedComplexIntegerRing_mem_iff_fraction ideal value).mpr
    ⟨⟨(denominator.val.val : ℂ) * value, hproduct⟩, denominator.val, denominator.property, ?_⟩
  change value = (denominator.val.val * value) / denominator.val.val
  exact (mul_div_cancel_left₀ value
    (isUnit_iff_ne_zero.mp (algebraicInteger_prime_complement_complex_unit ideal denominator))).symm

theorem centralCharacterScalar_mem_localizedComplexIntegerRing {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime]
    (algebraElement : MonoidAlgebra ℂ G)
    (hcoefficients : algebraElement ∈ groupAlgebraCoefficientSubring
      (localizedComplexIntegerRing ideal))
    (hcentral : ∀ other : MonoidAlgebra ℂ G, Commute algebraElement other)
    (label : basis.index) :
    centralCharacterScalar basis algebraElement label ∈ localizedComplexIntegerRing ideal := by
  exact localizedComplexIntegerRing_integral_mem ideal _
    (centralCharacterScalar_isIntegral basis _ algebraElement hcoefficients hcentral label)

end CFSG.TwoRankLowerBound.Helpers

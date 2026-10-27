module

public import Mathlib
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasis
public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicIntegerResidue
public import CFSG.CharacterTheory.TwoRankLowerBound.LocalizedAlgebraicIntegers
public import CFSG.CharacterTheory.TwoRankLowerBound.GroupAlgebraUnitResidue
public import CFSG.CharacterTheory.TwoRankLowerBound.TwoSidedPermutation
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterHom
public import CFSG.Open.Defs

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def centralCoefficientLiftHom {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) : centralCoefficientSubring (G := G) ring →+* MonoidAlgebra ring G where
  toFun value := liftGroupAlgebraCoefficients ring value.val
    (centralCoefficientSubring_coefficients ring value)
  map_one' := by
    apply groupAlgebraCoefficientEmbedding_injective ring
    rw [liftGroupAlgebraCoefficients_map, map_one]
    rfl
  map_mul' left right := by
    apply groupAlgebraCoefficientEmbedding_injective ring
    rw [liftGroupAlgebraCoefficients_map, map_mul, liftGroupAlgebraCoefficients_map,
      liftGroupAlgebraCoefficients_map]
    rfl
  map_zero' := by
    apply groupAlgebraCoefficientEmbedding_injective ring
    rw [liftGroupAlgebraCoefficients_map, map_zero]
    rfl
  map_add' left right := by
    apply groupAlgebraCoefficientEmbedding_injective ring
    rw [liftGroupAlgebraCoefficients_map, map_add, liftGroupAlgebraCoefficients_map,
      liftGroupAlgebraCoefficients_map]
    rfl

theorem centralCoefficientLiftHom_map {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) (value : centralCoefficientSubring (G := G) ring) :
    MonoidAlgebra.mapRingHom G ring.subtype (centralCoefficientLiftHom ring value) = value.val :=
  liftGroupAlgebraCoefficients_map ring value.val (centralCoefficientSubring_coefficients ring value)

theorem centralCoefficientLiftHom_injective {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) : Function.Injective (centralCoefficientLiftHom (G := G) ring) := by
  intro left right hequal
  apply Subtype.ext
  have hembedded := congrArg (MonoidAlgebra.mapRingHom G ring.subtype) hequal
  rwa [centralCoefficientLiftHom_map, centralCoefficientLiftHom_map] at hembedded

theorem centralCoefficientLiftHom_scalar {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) :
    (centralCoefficientLiftHom (G := G) ring).comp (centralCoefficientScalarHom ring) =
      algebraMap ring (MonoidAlgebra ring G) := by
  apply RingHom.ext
  intro scalar
  apply groupAlgebraCoefficientEmbedding_injective ring
  rw [RingHom.comp_apply, centralCoefficientLiftHom_map]
  change algebraMap ℂ (MonoidAlgebra ℂ G) scalar.val =
    MonoidAlgebra.mapRingHom G ring.subtype (MonoidAlgebra.single 1 scalar)
  rw [MonoidAlgebra.mapRingHom_single]
  rfl

@[expose] noncomputable def centralCoefficientReductionHom {G : Type*} [Group G] [Fintype G]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] :
    centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal) →+*
      MonoidAlgebra (ComplexAlgebraicIntegers ⧸ ideal) G :=
  (MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal)).comp
    (centralCoefficientLiftHom _)

theorem groupAlgebra_leftMultiplicationCharpoly_map {ring target group : Type*}
    [CommRing ring] [CommRing target] [Group group] [Fintype group]
    (reduction : ring →+* target) (value : MonoidAlgebra ring group) :
    Polynomial.map reduction (LinearMap.charpoly (Algebra.lmul ring (MonoidAlgebra ring group) value)) =
      LinearMap.charpoly (Algebra.lmul target (MonoidAlgebra target group)
        (MonoidAlgebra.mapRingHom group reduction value)) := by
  rw [← LinearMap.charpoly_toMatrix _ (MonoidAlgebra.basis group ring),
    ← LinearMap.charpoly_toMatrix _ (MonoidAlgebra.basis group target), ← Matrix.charpoly_map]
  congr 1
  exact groupAlgebra_leftMultiplicationMatrix_map reduction value

theorem centralCoefficientLiftHom_charpoly_annihilates {G : Type*}
    [Group G] [Fintype G] (ring : Subring ℂ)
    (value : centralCoefficientSubring (G := G) ring) :
    Polynomial.eval₂ (centralCoefficientScalarHom ring) value
      (LinearMap.charpoly (Algebra.lmul ring (MonoidAlgebra ring G)
        (centralCoefficientLiftHom ring value))) = 0 := by
  apply centralCoefficientLiftHom_injective ring
  rw [Polynomial.hom_eval₂, centralCoefficientLiftHom_scalar, map_zero]
  exact Algebra.aeval_self_charpoly_lmul (centralCoefficientLiftHom ring value)

theorem centralCharacterResidueHom_zero_of_coefficient_reduction_zero {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (value : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal))
    (hzero : centralCoefficientReductionHom ideal value = 0) (label : basis.index) :
    centralCharacterResidueHom basis ideal label value = 0 := by
  let lifted := centralCoefficientLiftHom (localizedComplexIntegerRing ideal) value
  let polynomial := LinearMap.charpoly
    (Algebra.lmul (localizedComplexIntegerRing ideal)
      (MonoidAlgebra (localizedComplexIntegerRing ideal) G) lifted)
  have hannihilates := centralCoefficientLiftHom_charpoly_annihilates
    (localizedComplexIntegerRing ideal) value
  have hscalar := congrArg (centralCharacterResidueHom basis ideal label) hannihilates
  rw [Polynomial.hom_eval₂, map_zero] at hscalar
  have hcomposition : (centralCharacterResidueHom basis ideal label).comp
      (centralCoefficientScalarHom (localizedComplexIntegerRing ideal)) =
      localizedComplexIntegerResidue ideal := by
    apply RingHom.ext
    exact centralCharacterResidueHom_scalar basis ideal label
  rw [hcomposition] at hscalar
  have hpolynomial : Polynomial.map (localizedComplexIntegerResidue ideal) polynomial =
      Polynomial.X ^ Fintype.card G := by
    rw [groupAlgebra_leftMultiplicationCharpoly_map]
    change MonoidAlgebra.mapRingHom G (localizedComplexIntegerResidue ideal) lifted = 0 at hzero
    rw [hzero, map_zero,
      LinearMap.charpoly_zero (R := ComplexAlgebraicIntegers ⧸ ideal)
        (M := MonoidAlgebra (ComplexAlgebraicIntegers ⧸ ideal) G)]
    congr 1
    exact Module.finrank_eq_card_basis (MonoidAlgebra.basis G (ComplexAlgebraicIntegers ⧸ ideal))
  rw [← Polynomial.eval_map, hpolynomial, Polynomial.eval_pow, Polynomial.eval_X] at hscalar
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  exact (pow_eq_zero_iff Fintype.card_ne_zero).mp hscalar

theorem centralCoefficientReduction_kernel_le_characterResidue_kernel {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (label : basis.index) :
    RingHom.ker (centralCoefficientReductionHom (G := G) ideal) ≤
      RingHom.ker (centralCharacterResidueHom basis ideal label) := by
  intro value hvalue
  exact centralCharacterResidueHom_zero_of_coefficient_reduction_zero basis ideal value hvalue label

end CFSG.TwoRankLowerBound.Helpers

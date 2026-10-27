module

public import CFSG.CharacterTheory.TwoRankLowerBound.FixedPointComplementAction
public import CFSG.CharacterTheory.TwoRankLowerBound.LocalMatrixIdempotent
public import CFSG.CharacterTheory.TwoRankLowerBound.FixedCoordinateTraceElimination

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem fixedPointComplement_monoid_generator_fixedpointFree {group points : Type*}
    [Group group] [MulAction group points] (element : group)
    (hgenerator : ∀ member : group, ∃ exponent : ℕ, element ^ exponent = member) :
    ∀ point : ((MulAction.fixedPoints group points)ᶜ : Set points), element • point ≠ point := by
  intro point hequal
  apply point.property
  rw [MulAction.mem_fixedPoints]
  intro member
  obtain ⟨exponent, hexponent⟩ := hgenerator member
  rw [← hexponent]
  have hfixed : element • point.val = point.val := congrArg Subtype.val hequal
  clear hexponent
  induction exponent with
  | zero => rw [pow_zero, one_smul]
  | succ exponent hinduction => rw [pow_succ, mul_smul, hfixed, hinduction]

theorem finite_cyclic_zero_fixedBasis_trace {ring group points : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [CommGroup group] [Finite group]
    [MulAction group points] [Fintype points]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime group) (element : group)
    (hgenerator : ∀ member : group, ∃ exponent : ℕ, element ^ exponent = member)
    (projection : Module.End ring (MonoidAlgebra ring points))
    (hidempotent : IsIdempotentElem projection)
    (hcommute : Commute projection (Representation.ofMulAction ring group points element))
    (hzero : permutationFixedBasisReduction (group := group) (IsLocalRing.residue ring) projection = 0) :
    LinearMap.trace ring (MonoidAlgebra ring points)
      (projection * Representation.ofMulAction ring group points element) = 0 := by
  let fixed := MulAction.fixedPoints group points
  let equivalence := permutationSubsetCoordinates (ring := ring) fixed
  let transformed := (LinearEquiv.conjAlgEquiv ring equivalence) projection
  let translation := Representation.ofMulAction ring group (fixedᶜ : Set points) element
  have htranslation : (LinearEquiv.conjAlgEquiv ring equivalence)
      (Representation.ofMulAction ring group points element) = LinearMap.prodMap LinearMap.id translation :=
    permutationSubsetCoordinates_fixed_translation element
  have htransformedIdempotent : IsIdempotentElem transformed := by
    apply isIdempotentElem_iff.mpr
    change (LinearEquiv.conjAlgEquiv ring equivalence) projection *
      (LinearEquiv.conjAlgEquiv ring equivalence) projection = _
    rw [← map_mul, hidempotent.eq]
  have htransformedCommute : Commute transformed (LinearMap.prodMap LinearMap.id translation) := by
    have hequal := hcommute.map (LinearEquiv.conjAlgEquiv ring equivalence)
    rw [htranslation] at hequal
    exact hequal
  let coordinate := (LinearMap.fst ring (MonoidAlgebra ring fixed) (MonoidAlgebra ring (fixedᶜ : Set points))).comp
    (transformed.comp (LinearMap.inl ring (MonoidAlgebra ring fixed) (MonoidAlgebra ring (fixedᶜ : Set points))))
  have hcoordinateZero : permutationCoefficientExtension (IsLocalRing.residue ring) coordinate = 0 :=
    (fixedBasisReduction_eq_leftCoordinate_residue (IsLocalRing.residue ring) projection).trans hzero
  have hunit := local_permutation_one_sub_isUnit_of_residue_zero coordinate hcoordinateZero
  obtain ⟨remainder, hremainder, hremCommute, htrace⟩ := binary_projection_fixed_coordinate_elimination
    transformed htransformedIdempotent translation htransformedCommute hunit
  have hremGroup : ∀ member : group,
      Commute remainder (Representation.ofMulAction ring group (fixedᶜ : Set points) member) := by
    intro member
    obtain ⟨exponent, hexponent⟩ := hgenerator member
    rw [← hexponent, map_pow]
    exact hremCommute.pow_right exponent
  have hfixedpointFree := fixedPointComplement_monoid_generator_fixedpointFree
    (points := points) element hgenerator
  have hzeroTrace := finite_p_action_equivariant_summand_trace_zero prime hgroup element hfixedpointFree
    1 (1 : ringˣ) (1 : ringˣ) (by simp) IsPrimitiveRoot.one
    (1 : Module.End ring (MonoidAlgebra ring (fixedᶜ : Set points))) remainder
    (fun _ => Commute.one_left _) hremGroup (by simp) hremainder (Commute.one_right _)
  rw [mul_one] at hzeroTrace
  have hconjugate := LinearMap.trace_conj'
    (projection * Representation.ofMulAction ring group points element) equivalence
  change LinearMap.trace ring _ ((LinearEquiv.conjAlgEquiv ring equivalence)
    (projection * Representation.ofMulAction ring group points element)) = _ at hconjugate
  rw [map_mul, htranslation] at hconjugate
  exact hconjugate.symm.trans (htrace.trans hzeroTrace)

theorem cyclicPermutation_zero_fixedBasis_trace {ring points : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [Fintype points]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (primary : Equiv.Perm points) (exponent : ℕ) (hprimary : orderOf primary = prime ^ exponent)
    (projection : Module.End ring (MonoidAlgebra ring points))
    (hidempotent : IsIdempotentElem projection)
    (hcommute : Commute projection (Representation.ofMulAction ring (Equiv.Perm points) points primary))
    (hzero : permutationFixedBasisReduction (group := Subgroup.zpowers primary)
      (IsLocalRing.residue ring) projection = 0) :
    LinearMap.trace ring (MonoidAlgebra ring points)
      (projection * Representation.ofMulAction ring (Equiv.Perm points) points primary) = 0 := by
  let group := Subgroup.zpowers primary
  let : CommGroup group := IsCyclic.commGroup
  have hgroup : IsPGroup prime group := IsPGroup.of_card (by rw [Nat.card_zpowers, hprimary])
  let element : group := ⟨primary, Subgroup.mem_zpowers primary⟩
  have hgenerator : ∀ member : group, ∃ power : ℕ, element ^ power = member := by
    intro member
    obtain ⟨power, _, hequal⟩ := Finset.mem_image.mp
      (((isOfFinOrder_of_finite primary).mem_zpowers_iff_mem_range_orderOf).mp member.property)
    exact ⟨power, Subtype.ext hequal⟩
  have hrepresentation : Representation.ofMulAction ring group points element =
      Representation.ofMulAction ring (Equiv.Perm points) points primary := by
    apply LinearMap.ext
    intro value
    ext point
    simp only [Representation.coeff_ofMulAction]
    rfl
  have hcommute' : Commute projection (Representation.ofMulAction ring group points element) := by
    rw [hrepresentation]
    exact hcommute
  rw [← hrepresentation]
  exact finite_cyclic_zero_fixedBasis_trace prime hgroup element hgenerator projection hidempotent hcommute' hzero

end CFSG.TwoRankLowerBound.Helpers

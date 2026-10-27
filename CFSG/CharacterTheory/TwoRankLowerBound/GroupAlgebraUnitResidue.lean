module

public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianPGroupAlgebra
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupAlgebra_leftMultiplicationMatrix_apply {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (value : MonoidAlgebra ring group)
    (row column : group) :
    LinearMap.toMatrix (MonoidAlgebra.basis group ring) (MonoidAlgebra.basis group ring)
      (Algebra.lmul ring (MonoidAlgebra ring group) value) row column =
        value.coeff (row * column⁻¹) := by
  rw [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply]
  change (value * MonoidAlgebra.single column 1).coeff row = _
  simp only [MonoidAlgebra.coeff_mul_single_apply, mul_one]

theorem groupAlgebra_leftMultiplicationMatrix_map {ring target group : Type*}
    [CommRing ring] [CommRing target] [Group group] [Fintype group]
    (residue : ring →+* target) (value : MonoidAlgebra ring group) :
    residue.mapMatrix (LinearMap.toMatrix (MonoidAlgebra.basis group ring)
      (MonoidAlgebra.basis group ring) (Algebra.lmul ring (MonoidAlgebra ring group) value)) =
    LinearMap.toMatrix (MonoidAlgebra.basis group target) (MonoidAlgebra.basis group target)
      (Algebra.lmul target (MonoidAlgebra target group) (MonoidAlgebra.mapRingHom group residue value)) := by
  ext row column
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
    groupAlgebra_leftMultiplicationMatrix_apply, MonoidAlgebra.coeff_mapRingHom]

theorem groupAlgebra_leftMultiplicationDet_map {ring target group : Type*}
    [CommRing ring] [CommRing target] [Group group] [Finite group]
    (residue : ring →+* target) (value : MonoidAlgebra ring group) :
    residue (LinearMap.det (Algebra.lmul ring (MonoidAlgebra ring group) value)) =
      LinearMap.det (Algebra.lmul target (MonoidAlgebra target group)
        (MonoidAlgebra.mapRingHom group residue value)) := by
  let := Fintype.ofFinite group
  rw [← LinearMap.det_toMatrix (MonoidAlgebra.basis group ring), RingHom.map_det,
    groupAlgebra_leftMultiplicationMatrix_map, LinearMap.det_toMatrix]

theorem groupAlgebra_isUnit_iff_leftMultiplicationDet {ring group : Type*}
    [CommRing ring] [Group group] [Finite group] (value : MonoidAlgebra ring group) :
    IsUnit value ↔ IsUnit (LinearMap.det (Algebra.lmul ring (MonoidAlgebra ring group) value)) := by
  rw [← Algebra.lmul_isUnit_iff (R := ring)]
  exact LinearMap.isUnit_iff_isUnit_det _

theorem groupAlgebra_isUnit_iff_residue {ring target group : Type*}
    [CommRing ring] [CommRing target] [Group group] [Finite group]
    (residue : ring →+* target) (hdetect : ∀ coefficient, IsUnit (residue coefficient) ↔ IsUnit coefficient)
    (value : MonoidAlgebra ring group) :
    IsUnit (MonoidAlgebra.mapRingHom group residue value) ↔ IsUnit value := by
  rw [groupAlgebra_isUnit_iff_leftMultiplicationDet,
    ← groupAlgebra_leftMultiplicationDet_map, hdetect,
    ← groupAlgebra_isUnit_iff_leftMultiplicationDet]

theorem groupAlgebraAugmentation_map {ring target group : Type*}
    [CommSemiring ring] [CommSemiring target] [Monoid group] [Finite group]
    (residue : ring →+* target) (value : MonoidAlgebra ring group) :
    groupAlgebraAugmentation target group (MonoidAlgebra.mapRingHom group residue value) =
      residue (groupAlgebraAugmentation ring group value) := by
  let := Fintype.ofFinite group
  simp only [groupAlgebraAugmentation_sum, MonoidAlgebra.coeff_mapRingHom, map_sum]

theorem local_abelian_p_group_algebra_isUnit_iff {ring group : Type*}
    [CommRing ring] [IsLocalRing ring] [CommGroup group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime group) (value : MonoidAlgebra ring group) :
    IsUnit value ↔ IsUnit (groupAlgebraAugmentation ring group value) := by
  rw [← groupAlgebra_isUnit_iff_residue (IsLocalRing.residue ring)
    (fun coefficient => isUnit_iff_ne_zero.trans
      (IsLocalRing.residue_ne_zero_iff_isUnit coefficient)),
    abelian_p_group_algebra_isUnit_iff prime hgroup, groupAlgebraAugmentation_map,
    IsLocalRing.residue_ne_zero_iff_isUnit]

theorem local_abelian_p_group_algebra_unit_or_complement {ring group : Type*}
    [CommRing ring] [IsLocalRing ring] [CommGroup group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime group) (value : MonoidAlgebra ring group) :
    IsUnit value ∨ IsUnit (1 - value) := by
  rw [local_abelian_p_group_algebra_isUnit_iff prime hgroup,
    local_abelian_p_group_algebra_isUnit_iff prime hgroup, map_sub, map_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

end CFSG.TwoRankLowerBound.Helpers

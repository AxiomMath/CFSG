module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwap

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv statedDerivedReindexEquiv_symm_val)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (familyTransport familyTransport_orbit plusCoordinate_pointFamily
    stated_pointFamily_orbit_subset)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap (statedPointFamily_orbit_card)
open scoped Pointwise

section Scalar

variable {K : Type} [Field K] {d : ℕ}

theorem neg_one_mem_matrixIsometries (Q : QuadraticForm K (Fin d → K)) :
    (-1 : GL (Fin d) K) ∈ matrixIsometries Q := by
  rw [mem_matrixIsometries_iff]
  intro v
  rw [matrixLinearEquiv_apply, Units.val_neg, Units.val_one, Matrix.neg_mulVec,
    Matrix.one_mulVec, QuadraticMap.map_neg]

theorem isometryConjugationHom_neg_one (Q : QuadraticForm K (Fin d → K)) :
    isometryConjugationHom Q ⟨-1, neg_one_mem_matrixIsometries Q⟩ = 1 := by
  change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ⟨-1, _⟩) = 1
  rw [← map_one (matrixProjectiveConjugationHom Q)]
  refine matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar Q (-1) ?_ rfl
  change (-1 : GL (Fin d) K) = 1 * GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ)
  rw [one_mul]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem two_mul_relIndex_inner_le [Finite K] (Q : QuadraticForm K (Fin d → K))
    (hneg : (⟨-1, neg_one_mem_matrixIsometries Q⟩ : matrixIsometries Q) ∉
      commutator (matrixIsometries Q)) :
    2 * (inner (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range ≤
      Nat.card (Abelianization (matrixIsometries Q)) := by
  set N := (inner (matrixProjectiveDerived Q)).comap (isometryConjugationHom Q) with hN
  have hle : commutator (matrixIsometries Q) ≤ N := by
    rw [hN, ← Subgroup.map_le_iff_le_comap, inner_eq_map_commutator Q]
  have hmem : (⟨-1, neg_one_mem_matrixIsometries Q⟩ : matrixIsometries Q) ∈ N := by
    rw [hN, Subgroup.mem_comap, isometryConjugationHom_neg_one]
    exact one_mem _
  have hidx : (commutator (matrixIsometries Q)).index =
      Nat.card (Abelianization (matrixIsometries Q)) := rfl
  have h0 : (commutator (matrixIsometries Q)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.relIndex_mul_index hle
  have hrel0 : (commutator (matrixIsometries Q)).relIndex N ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact h0 hmul.symm
  have hrel1 : (commutator (matrixIsometries Q)).relIndex N ≠ 1 := fun h =>
    hneg (Subgroup.relIndex_eq_one.mp h hmem)
  rw [← Subgroup.index_comap, ← hN, ← hidx, ← hmul]
  exact Nat.mul_le_mul_right _ (by omega)

theorem neg_one_not_mem_statedOmega_quadMinus [Finite K] {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (h2 : (2 : K) ≠ 0) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hsq : IsSquare ((-1 : K) ^ n)) :
    (-1 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) ∉
      StatedOmega (StatedQuadMinus n K b c) := by
  have e1 : toLinEquiv (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K (-1) = LinearEquiv.neg K := by
    refine LinearEquiv.ext fun x => ?_
    rw [toLinEquiv_apply, Units.val_neg, Units.val_one, neg_mulVec, one_mulVec]
    rfl
  rw [statedOmega_eq_map_elementaryGroup (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus hn hirr), Subgroup.mem_map_equiv,
    MulEquiv.symm_symm, e1,
    CFSG.ClassicalInvolution.neg_mem_elementaryGroup_quadMinus_iff h2 hirr hn]
  obtain ⟨s, hs⟩ := hsq
  rintro ⟨d, hd⟩
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact pow_ne_zero n (neg_ne_zero.mpr one_ne_zero) hs
  have hmul : d * d = s * s * (b ^ 2 - 4 * c) := by
    rw [← hd, ← hs]
    rw [show (-1 : K) ^ n = (-1 : K) ^ (n - 1) * (-1) by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [pow_succ]]
    ring
  apply hirr ((d - b * s) / (2 * s))
  field_simp [hs0, h2]
  linear_combination hmul

end Scalar

theorem index_matrixProjectiveImage_plus_four {T : Type} [Group T] {p f : ℕ}
    (h : StatedClassicalModel T .POmegaPlus 4 p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) :
    (matrixProjectiveImage (coordinateQuadPlus 4 K)).index = 1 ∨
      (matrixProjectiveImage (coordinateQuadPlus 4 K)).index = 3 := by
  have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
      (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
    MulAction.index_stabilizer _ _
  rw [← coordinate_plus_family_eq_matrixImage h K hK e, hst, ← plusCoordinate_pointFamily,
    ← familyTransport_orbit, Set.ncard_image_of_injective _ (familyTransport _).injective,
    ← Nat.card_coe_set_eq]
  exact statedPointFamily_orbit_card 4 K (by norm_num)
    (stated_pointFamily_orbit_subset (K := K) rfl)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Model

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X11Char

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open LocalAnalysis.ComponentInitial.OrthogonalTail in
theorem exists_model_of_normal {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (hC : centralizer (N : Set H) = ⊥) {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hm : Blueprint.LieModel N .POmegaMinus 4 r e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K) (_ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (Θ : N ≃* projectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)),
      Nat.card K = r ^ e ∧ ∀ t : H, orderOf t = 2 →
        Nonempty (InvData N (coordinateQuadMinus 4 K (by norm_num) b c) Θ t) := by
  have hstated := GH74.statedClassicalModel_of_lieModel (by norm_num) hm
  obtain ⟨hadm, K, _, _, hK, b, c, hirr, ⟨φ⟩⟩ := id hstated
  have hn : 1 ≤ 4 := by norm_num
  set Q := coordinateQuadMinus 4 K hn b c with hQdef
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_minus hstated K hK b c hirr φ
  have hQ0 : ∃ v, Q v ≠ 0 := exists_ne_zero_of_polarBilin_nondegenerate Q hnd (by norm_num)
  set ψc := coordinateMinusWitnessEquiv K hn b c φ
  refine ⟨K, inferInstance, inferInstance, b, c, hirr, ψc.trans (projectiveEquiv Q hQ0), hK,
    fun t ht => ?_⟩
  have hker := RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff Q hnd
    hT hAP
  set α := MulAut.congr ψc (MulAut.conjNormal t) with hαdef
  obtain ⟨g, hg⟩ : α ∈ matrixProjectiveImage Q :=
    CatalogueBOrthogonalInvolutionConjugacy.mem_image_of_familyAut_eq_top
      (orthogonal_geometry_tail_model_point_family_invariant
        N .POmegaMinus (.inr rfl) 4 r e hstated hn K hK b c hirr).2
      (coordinate_minus_family_eq_matrixImage hstated hn K hK b c hirr φ) α
  have hord : orderOf (matrixProjectiveConjugationHom Q g) = 2 := by
    rw [hg, hαdef]
    have h1 := orderOf_injective (MulAut.congr ψc).toMonoidHom (MulAut.congr ψc).injective
      (MulAut.conjNormal t)
    have h2 := orderOf_injective _ (conjNormal_injective N hC) t
    exact h1.trans (h2.trans ht)
  have hgg : matrixProjectiveConjugationHom Q (g * g) = 1 := by
    rw [map_mul, ← pow_two]
    have h := pow_orderOf_eq_one (matrixProjectiveConjugationHom Q g)
    rwa [hord] at h
  obtain ⟨hright, a, ha⟩ := (hker (g * g)).mp hgg
  obtain ⟨hl, hr'⟩ := CatalogueBOrthogonalInvolutionRepresentation.sq_val Q g
  have hσ2 : g.val.right ^ 2 = 1 := hr' ▸ hright
  have hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin (2 * 4)) K g.val.right
      g.val.left = GeneralLinearGroup.scalar (Fin (2 * 4)) a := by rw [← hl, ha]
  have hp := hadm.1
  have hg1 : g.val.right = 1 := by
    by_contra hσ1
    exact false_of_field_pair hp hr2 he hK hirr hnd g hσ2 hσ1 a hc
  set A := matrixLinearEquiv g.val.left with hAdef
  have hsim := matrix_similarity Q g hg1
  have hsq : ∀ x, A (A x) = (a : K) • x := by
    intro x
    have h := coordinateSemilinearMap_sq_apply g.val a hσ2 hc x
    rwa [coordinateSemilinearMap_eq_matrix g.val hg1] at h
  have hns : ∀ a' : Kˣ, GeneralLinearGroup.scalar (Fin (2 * 4)) a' ≠ g.val.left := by
    intro a' ha'
    have h1 : matrixProjectiveConjugationHom Q g = 1 := (hker g).mpr ⟨hg1, a', ha'.symm⟩
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hnonscalar := matrixLinearEquiv_ne_smul_one g.val.left hns
  have hμ : (multiplier Q g : K) = a :=
    multiplier_eq_of_not_isPlusType r e hr hr2 he hK Q hnd (by simp)
      (not_isPlusType_coordinateQuadMinus 4 hn hirr) A a (multiplier Q g) hsq
      (polar_similarity Q A (multiplier Q g) hsim) hnonscalar
  refine ⟨⟨A, multiplier Q g, a, hsim, hsq, hμ, hnonscalar, fun x => ?_⟩⟩
  change projectiveEquiv Q hQ0 (ψc (MulAut.conjNormal t x)) = _
  have h1 : ψc (MulAut.conjNormal t x) = α (ψc x) := by
    rw [hαdef, MulAut.congr_apply]
    simp
  rw [h1, ← hg]
  exact projectiveEquiv_conjugation_linear Q hQ0 g hg1 (ψc x)

end CFSG.ComponentClassification.CatLeafProof.X11Char

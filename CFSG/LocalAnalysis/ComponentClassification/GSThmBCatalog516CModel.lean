module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Field
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Neg
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.GSThmB.Catalog7Std

theorem one_le_four' : 1 ≤ 4 := by norm_num

abbrev qM (K : Type) [Field K] (b c : K) : QuadraticForm K (Fin (2 * 4) → K) :=
  coordinateQuadMinus 4 K one_le_four' b c

theorem qM_ne_zero {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : ∃ v, qM K b c v ≠ 0 :=
  exists_ne_zero_of_polarBilin_nondegenerate _
    (regular_coordinateQuadMinus (n := 4) K b c (le_refl 4) hirr).1 (by norm_num)

@[expose] def thetaOf {L : Type} [Group L] {K : Type} [Field K] {b c : K}
    (φ : L ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) (hQ0 : ∃ v, qM K b c v ≠ 0) :
    L ≃* projectiveDerived (qM K b c) :=
  (coordinateMinusWitnessEquiv K one_le_four' b c φ).trans (projectiveEquiv _ hQ0)

structure AutModel {L : Type} [Group L] {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (Θ : L ≃* projectiveDerived Q) (α : MulAut L) where
  g : similarityPairs Q
  hg : g.val.right = 1
  c : Kˣ
  hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) = (c : K) • x
  hμc : (multiplier Q g : K) = c
  hns : ∀ a : K, (matrixLinearEquiv g.val.left).toLinearMap ≠ a • (1 : Module.End K (Fin d → K))
  hconj : ∀ x, Θ (α x) = projectiveConjugation Q (matrixLinearEquiv g.val.left) (multiplier Q g)
    (matrix_similarity Q g hg) (Θ x)
  hinner : (∃ x, α = MulAut.conj x) →
    ∃ a : Kˣ, ∃ D ∈ matrixDerived Q, g.val.left = D * GeneralLinearGroup.scalar (Fin d) a

section Inner

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem inl_mem_similarityPairs {D : GL (Fin d) K} (hD : D ∈ matrixDerived Q) :
    SemidirectProduct.inl D ∈ similarityPairs Q := by
  refine ⟨1, fun v => ?_⟩
  rw [coordinateSemilinearMap_eq_matrix _ (SemidirectProduct.right_inl D)]
  have h := matrixDerived_le_isometries Q hD
  change matrixLinearIso D ∈ TauCeti.QuadraticMap.orthogonalGroup Q at h
  have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp h v
  change Q (matrixLinearEquiv D v) = (1 : K) * (1 : K ≃+* K) (Q v)
  rw [one_mul]
  exact h1

theorem matrixProjectiveConjugation_inl {D : GL (Fin d) K} (hD : D ∈ matrixDerived Q) :
    matrixProjectiveConjugation Q ⟨_, inl_mem_similarityPairs Q hD⟩ =
      MulAut.conj (matrixProjectiveProjection Q ⟨D, hD⟩) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q x
  rw [matrixProjectiveConjugation_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

end Inner

open LocalAnalysis.ComponentInitial.OrthogonalTail in
theorem exists_autModel {L : Type} [Group L] {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hstated : StatedClassicalModel L .POmegaMinus 4 r e) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = r ^ e) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (φ : L ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) (hQ0 : ∃ v, qM K b c v ≠ 0)
    (α : MulAut L) (hα : orderOf α = 2) : Nonempty (AutModel (qM K b c) (thetaOf φ hQ0) α) := by
  set Q := qM K b c with hQdef
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_minus hstated K hK b c hirr φ
  have hker := RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff Q hnd
    hT hAP
  set ψc := coordinateMinusWitnessEquiv K one_le_four' b c φ
  set α' := MulAut.congr ψc α with hα'def
  obtain ⟨g, hg⟩ : α' ∈ matrixProjectiveImage Q :=
    CatalogueBOrthogonalInvolutionConjugacy.mem_image_of_familyAut_eq_top
      (orthogonal_geometry_tail_model_point_family_invariant
        L .POmegaMinus (.inr rfl) 4 r e hstated one_le_four' K hK b c hirr).2
      (coordinate_minus_family_eq_matrixImage hstated one_le_four' K hK b c hirr φ) α'
  have hord : orderOf (matrixProjectiveConjugationHom Q g) = 2 := by
    rw [hg, hα'def]
    exact (orderOf_injective (MulAut.congr ψc).toMonoidHom (MulAut.congr ψc).injective α).trans hα
  have hgg : matrixProjectiveConjugationHom Q (g * g) = 1 := by
    rw [map_mul, ← pow_two]
    have h := pow_orderOf_eq_one (matrixProjectiveConjugationHom Q g)
    rwa [hord] at h
  obtain ⟨hright, a, ha⟩ := (hker (g * g)).mp hgg
  obtain ⟨hl, hr'⟩ := CatalogueBOrthogonalInvolutionRepresentation.sq_val Q g
  have hσ2 : g.val.right ^ 2 = 1 := hr' ▸ hright
  have hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin (2 * 4)) K g.val.right
      g.val.left = GeneralLinearGroup.scalar (Fin (2 * 4)) a := by rw [← hl, ha]
  have hg1 : g.val.right = 1 := by
    by_contra hσ1
    exact Om8.false_of_field_pair hr hr2 he hK hirr hnd g hσ2 hσ1 a hc
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
    Om8.multiplier_eq_of_not_isPlusType r e hr hr2 he hK Q hnd (by simp)
      (Om8.not_isPlusType_coordinateQuadMinus 4 one_le_four' hirr) A a (multiplier Q g) hsq
      (polar_similarity Q A (multiplier Q g) hsim) hnonscalar
  refine ⟨⟨g, hg1, a, hsq, hμ, hnonscalar, fun x => ?_, ?_⟩⟩
  · change projectiveEquiv Q hQ0 (ψc (α x)) = _
    have h1 : ψc (α x) = α' (ψc x) := by
      rw [hα'def, MulAut.congr_apply]
      simp
    rw [h1, ← hg]
    exact projectiveEquiv_conjugation_linear Q hQ0 g hg1 (ψc x)
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨D, hD⟩, hDx⟩ := matrixProjectiveProjection_surjective Q (ψc x)
    have hconjD : α' = MulAut.conj (ψc x) := by
      apply MulEquiv.ext
      intro y
      rw [hα'def, MulAut.congr_apply, MulAut.conj_apply]
      simp [MulAut.conj_apply]
    set gD : similarityPairs Q := ⟨_, inl_mem_similarityPairs Q hD⟩
    have h1 : matrixProjectiveConjugationHom Q (gD⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hg, hconjD, ← hDx]
      change (matrixProjectiveConjugation Q gD)⁻¹ * _ = 1
      rw [matrixProjectiveConjugation_inl Q hD, inv_mul_cancel]
    obtain ⟨-, a', ha'⟩ := (hker _).mp h1
    refine ⟨a', D, hD, ?_⟩
    have h2 : (gD⁻¹ * g).val.left = D⁻¹ * g.val.left := by
      change ((SemidirectProduct.inl D)⁻¹ * g.val).left = _
      rw [← map_inv, coordinateSemilinearGroup_mul_matrix, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one]
      rfl
    rw [h2] at ha'
    rw [← ha', mul_inv_cancel_left]

end CFSG.ComponentClassification.GSThmB.Cent516

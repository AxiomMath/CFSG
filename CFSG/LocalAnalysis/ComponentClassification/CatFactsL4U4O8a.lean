module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Field
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Neg
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.GroupTheory.WeirSylow (IsPlusType)

variable (K : Type) [Field K] (b c : K)

abbrev G0 : Type := StatedProj (StatedOmega (StatedQuadMinus 4 K b c))

abbrev Q8 : QuadraticForm K (Fin (2 * 4) → K) := coordinateQuadMinus 4 K (by norm_num) b c

abbrev psiC : G0 K b c ≃* matrixProjectiveDerived (Q8 K b c) :=
  coordinateMinusWitnessEquiv K (n := 4) (by norm_num) b c (MulEquiv.refl _)

abbrev theta (hQ0 : ∃ v, Q8 K b c v ≠ 0) : G0 K b c ≃* projectiveDerived (Q8 K b c) :=
  (psiC K b c).trans (projectiveEquiv (Q8 K b c) hQ0)

variable [Finite K]

theorem stated {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    StatedClassicalModel (G0 K b c) .POmegaMinus 4 p e :=
  ⟨⟨hp, he, le_rfl⟩, K, inferInstance, inferInstance, hK, b, c, hirr, ⟨MulEquiv.refl _⟩⟩

theorem exists_ne_zero {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : ∃ v, Q8 K b c v ≠ 0 := by
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_minus (stated K b c hp he hK hirr) K hK b c hirr
    (MulEquiv.refl _)
  exact exists_ne_zero_of_polarBilin_nondegenerate (Q8 K b c) hnd (by norm_num)

open LocalAnalysis.ComponentInitial.OrthogonalTail in
theorem exists_pair {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ψ : MulAut (G0 K b c)) :
    ∃ g : similarityPairs (Q8 K b c),
      matrixProjectiveConjugationHom (Q8 K b c) g = MulAut.congr (psiC K b c) ψ := by
  have hstated := stated K b c hp he hK hirr
  exact CatalogueBOrthogonalInvolutionConjugacy.mem_image_of_familyAut_eq_top
    ((orthogonal_geometry_tail_model_point_family_invariant (G0 K b c) .POmegaMinus (.inr rfl)
      4 p e hstated (by norm_num) K hK b c hirr).2)
    (coordinate_minus_family_eq_matrixImage hstated (by norm_num) K hK b c hirr (MulEquiv.refl _))
    _

omit [Finite K] in
theorem theta_map (hQ0 : ∃ v, Q8 K b c v ≠ 0) (ψ : MulAut (G0 K b c))
    (g : similarityPairs (Q8 K b c))
    (hg : matrixProjectiveConjugationHom (Q8 K b c) g = MulAut.congr (psiC K b c) ψ)
    (hg1 : g.val.right = 1) (x : G0 K b c) :
    theta K b c hQ0 (ψ x) = projectiveConjugation (Q8 K b c) (matrixLinearEquiv g.val.left)
      (multiplier (Q8 K b c) g) (matrix_similarity (Q8 K b c) g hg1) (theta K b c hQ0 x) := by
  change projectiveEquiv (Q8 K b c) hQ0 (psiC K b c (ψ x)) = _
  have h1 : psiC K b c (ψ x) = MulAut.congr (psiC K b c) ψ (psiC K b c x) := by
    rw [MulAut.congr_apply]
    simp
  rw [h1, ← hg]
  exact projectiveEquiv_conjugation_linear (Q8 K b c) hQ0 g hg1 (psiC K b c x)

theorem exists_simil {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hQ0 : ∃ v, Q8 K b c v ≠ 0) (φ : MulAut (G0 K b c)) (hφ2 : φ ^ 2 = 1) (hφ1 : φ ≠ 1) :
    ∃ (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ c₀ : Kˣ)
      (hsim : ∀ x, Q8 K b c (A x) = (μ : K) * Q8 K b c x),
      (∀ x, A (A x) = (c₀ : K) • x) ∧ (μ : K) = c₀ ∧
        (∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K (Fin (2 * 4) → K))) ∧
        (∀ x, theta K b c hQ0 (φ x) =
          projectiveConjugation (Q8 K b c) A μ hsim (theta K b c hQ0 x)) ∧
        ∃ gφ : similarityPairs (Q8 K b c),
          matrixProjectiveConjugationHom (Q8 K b c) gφ = MulAut.congr (psiC K b c) φ ∧
            gφ.val.right = 1 ∧ A = matrixLinearEquiv gφ.val.left := by
  have hstated := stated K b c hp he hK hirr
  obtain ⟨-, hnd, hT, -, hAP, -⟩ :=
    coordinate_model_witness_minus hstated K hK b c hirr (MulEquiv.refl _)
  have hker := RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff
    (Q8 K b c) hnd hT hAP
  obtain ⟨g, hg⟩ := exists_pair K b c hp he hK hirr φ
  have hord : orderOf (matrixProjectiveConjugationHom (Q8 K b c) g) = 2 := by
    rw [hg]
    exact (orderOf_injective (MulAut.congr (psiC K b c)).toMonoidHom
      (MulAut.congr (psiC K b c)).injective φ).trans (orderOf_eq_prime hφ2 hφ1)
  have hgg : matrixProjectiveConjugationHom (Q8 K b c) (g * g) = 1 := by
    rw [map_mul, ← pow_two]
    have h := pow_orderOf_eq_one (matrixProjectiveConjugationHom (Q8 K b c) g)
    rwa [hord] at h
  obtain ⟨hright, a, ha⟩ := (hker (g * g)).mp hgg
  obtain ⟨hl, hr'⟩ := CatalogueBOrthogonalInvolutionRepresentation.sq_val (Q8 K b c) g
  have hσ2 : g.val.right ^ 2 = 1 := hr' ▸ hright
  have hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin (2 * 4)) K g.val.right
      g.val.left = GeneralLinearGroup.scalar (Fin (2 * 4)) a := by rw [← hl, ha]
  have hg1 : g.val.right = 1 := by
    by_contra hσ1
    exact GSThmB.Catalog7Std.Om8.false_of_field_pair hp hp2 he hK hirr hnd g hσ2 hσ1 a hc
  set A := matrixLinearEquiv g.val.left with hAdef
  have hsim := matrix_similarity (Q8 K b c) g hg1
  have hsq : ∀ x, A (A x) = (a : K) • x := by
    intro x
    have h := coordinateSemilinearMap_sq_apply g.val a hσ2 hc x
    rwa [coordinateSemilinearMap_eq_matrix g.val hg1] at h
  have hns : ∀ a' : Kˣ, GeneralLinearGroup.scalar (Fin (2 * 4)) a' ≠ g.val.left := by
    intro a' ha'
    have h1 : matrixProjectiveConjugationHom (Q8 K b c) g = 1 := (hker g).mpr ⟨hg1, a', ha'.symm⟩
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hnonscalar := matrixLinearEquiv_ne_smul_one g.val.left hns
  have hμ : (multiplier (Q8 K b c) g : K) = a :=
    GSThmB.Catalog7Std.Om8.multiplier_eq_of_not_isPlusType p e hp hp2 he hK (Q8 K b c) hnd
      (by simp) (GSThmB.Catalog7Std.Om8.not_isPlusType_coordinateQuadMinus 4 (by norm_num) hirr)
      A a (multiplier (Q8 K b c) g) hsq
      (polar_similarity (Q8 K b c) A (multiplier (Q8 K b c) g) hsim) hnonscalar
  exact ⟨A, multiplier (Q8 K b c) g, a, hsim, hsq, hμ, hnonscalar,
    theta_map K b c hQ0 φ g hg hg1, g, hg, hg1, rfl⟩

end OIO

end CFSG.ComponentClassification.CatFactsL4U4

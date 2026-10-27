module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5OmegaD
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5OmegaInv

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5.Omega

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.ComponentClassification.SolMax.FiveCat.C5Omega
  (le_four_of_modelIn_orthTuples similarityConjugation_involutive)

theorem noLitLayer_field {K : Type} [Field K] [Finite K] {d f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 5 ^ f) (hdim : d = 2 * n + 1 ∧ 3 ≤ n ∨ d = 2 * n ∧ 4 ≤ n)
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate) (g : similarityPairs Q)
    (hσ2 : g.val.right ^ 2 = 1) (hσ : g.val.right ≠ 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c) :
    NoLitLayer ↥(fixedSubgroup (matrixProjectiveConjugationHom Q g)) := by
  intro L hL
  obtain ⟨hcomp, hA, -⟩ := hL
  have hmodel := CatLeafProof.odd_omega_field_modelIn Nat.prime_five (by norm_num) hf hK hdim hQ
    g hσ2 hσ c hc hcomp
  obtain ⟨hd4, -⟩ := le_four_of_modelIn_orthTuples hmodel hA
  omega

theorem litUnique_linear {K : Type} [Field K] [Finite K] {d f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 5 ^ f) (hd : 7 ≤ d) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (g : similarityPairs Q) (hg : g.val.right = 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c)
    (hns : ∀ a : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left) :
    LitUnique ↥(fixedSubgroup (matrixProjectiveConjugationHom Q g)) := by
  have : Nontrivial (Fin d → K) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [Module.finrank_fin_fun]; omega)
  have hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) = (c : K) • x := by
    intro x
    have h := coordinateSemilinearMap_sq_apply g.val c (by rw [hg, one_pow]) hc x
    rwa [coordinateSemilinearMap_eq_matrix g.val hg] at h
  have hnonscalar := matrixLinearEquiv_ne_smul_one g.val.left hns
  have hsim := matrix_similarity Q g hg
  let Φ := linearFixedEquiv Q (exists_ne_zero_of_polarBilin_nondegenerate Q hQ (by omega)) g hg
  refine LitUnique.of_mulEquiv Φ ?_
  refine litUnique_of_normalQuotient (orthogonalDerived Q) (scalarSigns Q)
    (scalarSigns_central Q)
    (similarityConjugation Q (matrixLinearEquiv g.val.left) (multiplier Q g) hsim)
    (fun x => similarityConjugation_involutive Q _ _ hsim c hsq x)
    (orthogonalDerived_invariant Q _ (multiplier Q g) hsim)
    (scalarSigns_invariant Q _ (multiplier Q g) hsim) ?_
  have h1 := liftedLitUnique_orthogonalOperatorCentralizer hf hK
    (by rw [Module.finrank_fin_fun]; exact hd) Q hQ (matrixLinearEquiv g.val.left) c
    (multiplier Q g) hsq (polar_similarity Q _ (multiplier Q g) hsim) hnonscalar
  exact (LiftedLitUnique.of_mulEquiv
    (fixedCentralizerEquiv Q (matrixLinearEquiv g.val.left) (multiplier Q g) hsim) h1).congr
    (fun x => Iff.rfl)

theorem litUnique_involution {K : Type} [Field K] [Finite K] {d f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 5 ^ f) (hdim : d = 2 * n + 1 ∧ 3 ≤ n ∨ d = 2 * n ∧ 4 ≤ n)
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hrep : SemilinearRepresentation Q) (α : MulAut (matrixProjectiveDerived Q))
    (hα2 : α * α = 1) (hα1 : α ≠ 1) : LitUnique ↥(fixedSubgroup α) := by
  obtain ⟨β, g, hg, hσ2, ⟨c, hc⟩, hns, -⟩ := hrep.2 α hα2 hα1
  refine LitUnique.of_mulEquiv
    ((CatalogueBOrthogonalInvolutionFixedComponents.conjFixedEquiv α β).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hg))) ?_
  by_cases hσ : g.val.right = 1
  · exact litUnique_linear hf hK (by omega) Q hQ g hσ c hc (hns hσ)
  · exact (noLitLayer_field hf hK hdim Q hQ g hσ2 hσ c hc).litUnique

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5.Omega

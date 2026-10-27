module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaLin
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaField
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport

public noncomputable section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.GroupTheory.WeirSylow (IsPlusType)

section Transport

variable {d : ℕ} {K : Type} [Field K]

theorem omega_a6Hyp_linear (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (g : similarityPairs Q) (hg : g.val.right = 1) [Finite (matrixProjectiveDerived Q)]
    {D : Subgroup ↥(fixedSubgroup (matrixProjectiveConjugationHom Q g))}
    (h : A6Hyp (matrixProjectiveConjugationHom Q g) D) :
    ∃ D' : Subgroup ↥(fixedSubgroup (projectiveConjugation Q (matrixLinearEquiv g.val.left)
      (multiplier Q g) (matrix_similarity Q g hg))),
      A6Hyp (projectiveConjugation Q (matrixLinearEquiv g.val.left) (multiplier Q g)
        (matrix_similarity Q g hg)) D' := by
  have key : ∀ τ : MulAut (projectiveDerived Q),
      τ = projectiveConjugation Q (matrixLinearEquiv g.val.left) (multiplier Q g)
        (matrix_similarity Q g hg) →
      ∀ D₁ : Subgroup ↥(fixedSubgroup τ), A6Hyp τ D₁ →
      ∃ D' : Subgroup ↥(fixedSubgroup (projectiveConjugation Q (matrixLinearEquiv g.val.left)
        (multiplier Q g) (matrix_similarity Q g hg))),
        A6Hyp (projectiveConjugation Q (matrixLinearEquiv g.val.left) (multiplier Q g)
          (matrix_similarity Q g hg)) D' := by
    rintro τ rfl D₁ h₁
    exact ⟨D₁, h₁⟩
  exact key _ (mulAutCongr_conjugation_linear Q hQ g hg) _
    (a6Hyp_congr (projectiveEquiv Q hQ) (matrixProjectiveConjugationHom Q g) D h)

end Transport

section XCore

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem omega_X_core
    {K : Type} [Field K] [Finite K] {d f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (hdim : d = 2 * n + 1 ∧ 3 ≤ n ∨ d = 2 * n ∧ 4 ≤ n)
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hrep : SemilinearRepresentation Q) [Finite (matrixProjectiveDerived Q)]
    (hO : LieOrderFormulasInput) (σ : MulAut (matrixProjectiveDerived Q)) (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) :
    f = 1 ∧ (d = 7 ∨ (d = 8 ∧ ¬ IsPlusType Q)) := by
  have hd7 : 7 ≤ d := by omega
  have hσ2 : σ * σ = 1 := by
    have h := pow_orderOf_eq_one σ
    rw [hσ] at h
    rwa [← pow_two]
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    omega
  obtain ⟨β, g, hg, hgσ2, ⟨c, hc⟩, hlin, -⟩ := hrep.2 σ hσ2 hσ1
  have hD' : ∃ D' : Subgroup ↥(fixedSubgroup (matrixProjectiveConjugationHom Q g)),
      A6Hyp (matrixProjectiveConjugationHom Q g) D' := by
    have key : ∀ τ : MulAut (matrixProjectiveDerived Q), τ = matrixProjectiveConjugationHom Q g →
        ∀ D₁ : Subgroup ↥(fixedSubgroup τ), A6Hyp τ D₁ →
        ∃ D' : Subgroup ↥(fixedSubgroup (matrixProjectiveConjugationHom Q g)),
          A6Hyp (matrixProjectiveConjugationHom Q g) D' := by
      rintro τ rfl D₁ h₁
      exact ⟨D₁, h₁⟩
    exact key _ ((MulEquiv.ext fun _ => rfl : MulAut.congr β⁻¹ σ = β⁻¹ * σ * β).trans hg) _
      (a6Hyp_congr β⁻¹ σ D hD)
  obtain ⟨D', hD'⟩ := hD'
  by_cases hright : g.val.right = 1
  · have hQ' : ∃ v, Q v ≠ 0 := exists_ne_zero_of_polarBilin_nondegenerate Q hQ (by omega)
    obtain ⟨D'', hD''⟩ := omega_a6Hyp_linear Q hQ' g hright hD'
    have hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) =
        (c : K) • x := by
      intro x
      have h := coordinateSemilinearMap_sq_apply g.val c (by rw [hright, one_pow]) hc x
      rwa [coordinateSemilinearMap_eq_matrix g.val hright] at h
    have hnonscalar := matrixLinearEquiv_ne_smul_one g.val.left (hlin hright)
    have hfin : finrank K (Fin d → K) = d := Module.finrank_fin_fun K
    have hfinite : Finite (projectiveDerived Q) :=
      Finite.of_equiv _ (projectiveEquiv Q hQ').toEquiv
    have := omega_linear_core (V := Fin d → K) hf hK hO Q hQ (matrixLinearEquiv g.val.left) c
      (multiplier Q g) hsq (matrix_similarity Q g hright) hnonscalar (by rw [hfin]; exact hd7)
      hD''
    rwa [hfin] at this
  · obtain ⟨hDc, hDA⟩ := hD'.component
    exact (omega_field_false Nat.prime_three (by norm_num) hf hK hdim hQ g hgσ2 hright c hc hO
      hDc hDA).elim

end XCore

end CFSG.ComponentClassification.CatFC

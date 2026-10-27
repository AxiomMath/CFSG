module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOmLin
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOmField

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare (orthogonalOperatorCentralizer)

theorem u42_omega_false {K : Type} [Field K] [Finite K] {d f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (hd : 7 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) (hidx : (orthogonalDerived Q).index = 4)
    (hrep : SemilinearRepresentation Q) {σ : MulAut (matrixProjectiveDerived Q)}
    (hσ : orderOf σ = 2) {J : Subgroup ↥(fixedSubgroup σ)} (hJ : U42Hyp σ J) : False := by
  have hK2 : (2 : K) ≠ 0 := Ring.two_ne_zero (u42_ringChar_ne_two hf hK)
  have h2 : σ * σ = 1 := by
    have h := pow_orderOf_eq_one σ
    rw [hσ, pow_two] at h
    exact h
  have h1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨β, g, hg, hσ2, ⟨c, hc⟩, hnsc, -⟩ := hrep.2 σ h2 h1
  have hconj : MulAut.congr β⁻¹ σ = matrixProjectiveConjugationHom Q g :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr β⁻¹ σ = β⁻¹ * σ * β).trans hg
  obtain ⟨J₂, hJ₂⟩ := U42Hyp.exists_of_eq hconj (U42Hyp.congr β⁻¹ σ J hJ)
  by_cases hg1 : g.val.right = 1
  ·
    have hex := exists_ne_zero_of_polarBilin_nondegenerate Q hQ (by omega)
    have hsim := matrix_similarity Q g hg1
    have hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) =
        (c : K) • x := by
      intro x
      have h := coordinateSemilinearMap_sq_apply g.val c (by rw [hg1, one_pow]) hc x
      rwa [coordinateSemilinearMap_eq_matrix g.val hg1] at h
    haveI : Finite (matrixProjectiveDerived Q) := by
      haveI := u42_finite_orthogonalGroup Q
      exact Finite.of_equiv _ (projectiveEquiv Q hex).symm.toEquiv
    obtain ⟨J₃, hJ₃⟩ := U42Hyp.of_intertwining (projectiveEquiv Q hex) _ _
      (projectiveEquiv_conjugation_linear Q hex g hg1) hJ₂
    have hbounds := u42_omega_fixed_bounds Q hK2 hidx
      (similarityConjugation Q (matrixLinearEquiv g.val.left) (multiplier Q g) hsim)
      (orthogonalDerived_invariant Q (matrixLinearEquiv g.val.left) (multiplier Q g) hsim)
      (scalarSigns_invariant Q (matrixLinearEquiv g.val.left) (multiplier Q g) hsim) hJ₃
    have hcardF : Nat.card (fixedSubgroup (similarityConjugation Q (matrixLinearEquiv g.val.left)
        (multiplier Q g) hsim)) =
        Nat.card (orthogonalOperatorCentralizer Q (matrixLinearEquiv g.val.left).toLinearMap) :=
      Nat.card_congr (fixedCentralizerEquiv Q (matrixLinearEquiv g.val.left) (multiplier Q g)
        hsim).toEquiv
    rw [hcardF] at hbounds
    exact u42_omega_linear_false hf hK Q hQ (matrixLinearEquiv g.val.left) c (multiplier Q g) hsq
      (polar_similarity Q (matrixLinearEquiv g.val.left) (multiplier Q g) hsim)
      (matrixLinearEquiv_ne_smul_one g.val.left (hnsc hg1))
      (by rw [Module.finrank_fin_fun]; exact hd) hbounds.1 hbounds.2.1 hbounds.2.2
  ·
    exact u42_omega_field_false hf hK hd hQ hidx g hσ2 hg1 c hc hJ₂

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

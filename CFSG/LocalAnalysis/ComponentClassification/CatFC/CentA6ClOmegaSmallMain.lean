module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallCount
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallCent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport

public section

namespace CFSG.ComponentClassification.CatFC.OmegaSmall

open Module Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare (orthogonalOperatorCentralizer)

section Transfer

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem omega_finite_orthogonalGroup (Q : QuadraticForm K (Fin d → K)) :
    Finite (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Finite.of_injective (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
    ((g.val : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) → (Fin d → K)))
    (fun a b h => Subtype.ext (LinearEquiv.coe_injective h))

theorem omega_linear_fixed_card_ge (hd : 0 < d) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (g : similarityPairs Q) (hg : g.val.right = 1) :
    Nat.card (matrixProjectiveDerived Q) *
        Nat.card (orthogonalOperatorCentralizer Q (matrixLinearEquiv g.val.left).toLinearMap) ≤
      Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  haveI := omega_finite_orthogonalGroup Q
  have hex := exists_ne_zero_of_polarBilin_nondegenerate Q hQ hd
  set A := matrixLinearEquiv g.val.left with hA
  set μ := multiplier Q g with hμ
  have hsim := matrix_similarity Q g hg
  have h1 : Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) =
      Nat.card (fixedSubgroup (projectiveConjugation Q A μ hsim)) :=
    Nat.card_congr (linearFixedEquiv Q hex g hg).toEquiv
  have h2 := card_fixed_normalCentralQuotient_ge (orthogonalDerived Q) (scalarSigns Q)
    (similarityConjugation Q A μ hsim) (orthogonalDerived_invariant Q A μ hsim)
    (scalarSigns_invariant Q A μ hsim)
  have h3 : Nat.card (fixedSubgroup (similarityConjugation Q A μ hsim)) =
      Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) :=
    Nat.card_congr (fixedCentralizerEquiv Q A μ hsim).toEquiv
  have h4 : Nat.card (matrixProjectiveDerived Q) = Nat.card (projectiveDerived Q) :=
    Nat.card_congr (projectiveEquiv Q hex).toEquiv
  rw [h1, h4, ← h3]
  exact h2

end Transfer

section Involution

open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K]

theorem omega_fixed_card_gt (hK : Nat.card K = 3) {d : ℕ} (hd : d = 7 ∨ d = 8)
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hrep : SemilinearRepresentation Q)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      4 * Nat.card (matrixProjectiveDerived Q))
    (σ : MulAut (matrixProjectiveDerived Q)) (hσ : orderOf σ = 2) :
    1440 < Nat.card (fixedSubgroup σ) := by
  have h2 : σ * σ = 1 := by
    have h := pow_orderOf_eq_one σ
    rw [hσ] at h
    rw [← pow_two]
    exact h
  have h1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨β, g, hg, hσ2, ⟨c, hc⟩, hns, hfield⟩ := hrep.2 σ h2 h1
  have hg1 : g.val.right = 1 := by
    by_contra hne
    obtain ⟨hcardK, -⟩ := hfield hne
    rw [hK] at hcardK
    rcases Nat.lt_or_ge (Nat.card {c : K // g.val.right c = c}) 2 with hm | hm
    · interval_cases (Nat.card {c : K // g.val.right c = c}) <;> omega
    · nlinarith
  have hcongr : Nat.card (fixedSubgroup σ) =
      Nat.card (fixedSubgroup (matrixProjectiveConjugationHom Q g)) := by
    have : MulAut.congr β⁻¹ σ = matrixProjectiveConjugationHom Q g := by
      rw [← hg]
      exact MulEquiv.ext fun _ => rfl
    rw [← this]
    exact Nat.card_congr (fixedEquiv β⁻¹ σ).toEquiv
  rw [hcongr]
  have hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) = (c : K) • x := by
    intro x
    have h := coordinateSemilinearMap_sq_apply g.val c (by rw [hg1, one_pow]) hc x
    rwa [coordinateSemilinearMap_eq_matrix g.val hg1] at h
  have hsim := matrix_similarity Q g hg1
  have hbig := omega_centralizer_card_gt hK (Module.finrank_fin_fun K) hd Q hQ
    (matrixLinearEquiv g.val.left) c (multiplier Q g) hsq
    (CatalogueBOrthogonalLinearFixed.polar_similarity Q (matrixLinearEquiv g.val.left)
      (multiplier Q g) hsim)
    (matrixLinearEquiv_ne_smul_one g.val.left (hns hg1))
  have hineq := omega_linear_fixed_card_ge (by omega) Q hQ g hg1
  rw [hcard] at hineq
  have hXpos : 0 < Nat.card (matrixProjectiveDerived Q) := Nat.card_pos
  have h5 : Nat.card (orthogonalOperatorCentralizer Q (matrixLinearEquiv g.val.left).toLinearMap) ≤
      4 * Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) := by
    refine Nat.le_of_mul_le_mul_left ?_ hXpos
    calc Nat.card (matrixProjectiveDerived Q) *
          Nat.card (orthogonalOperatorCentralizer Q (matrixLinearEquiv g.val.left).toLinearMap)
        ≤ Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) *
          (4 * Nat.card (matrixProjectiveDerived Q)) := hineq
      _ = Nat.card (matrixProjectiveDerived Q) *
          (4 * Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g))) := by ring
  exact (by omega : 1440 < Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)))

end Involution

end CFSG.ComponentClassification.CatFC.OmegaSmall

module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaX
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSplitDvd
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallDvd

public noncomputable section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

section Core

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem omega_linear_core_two (hK : Nat.card K = 3) (hO : LieOrderFormulasInput)
    (Q : QuadraticForm K V) [Finite (projectiveDerived Q)] (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (hnonscalar : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K V))
    (hd : finrank K V = 7 ∨ finrank K V = 8)
    {D : Subgroup ↥(fixedSubgroup (projectiveConjugation Q A μ hsim))}
    (hD : A6Hyp (projectiveConjugation Q A μ hsim) D) :
    2 ^ 9 ∣ Nat.card ↥(orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have hf : 1 ≤ 1 := le_rfl
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK]; norm_num
  have hsimP := polar_similarity Q A μ hsim
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨hsign, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure 3 1
      Nat.prime_three (by norm_num) hf hK' (by omega) Q hQ A c μ hsquare hsimP hnonscalar
  by_cases hsqc : IsSquare (c : K)
  · obtain ⟨r, hr⟩ := hsqc
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by simpa using hr)
    let b : Kˣ := Units.mk0 r hr0
    have hb : (c : K) = (b : K) ^ 2 := by rw [hr, sq]; rfl
    rcases hsign with hpos | hneg
    ·
      obtain ⟨hcompl, hV₁, hV₂, hpos', -⟩ := hsq b hb
      obtain ⟨-, hnd₁, hnd₂, e, -, -, -⟩ := hpos' hpos
      have h₁ : 1 ≤ finrank K (positiveSquareKernel A (b : K)) :=
        Submodule.one_le_finrank_iff.mpr hV₁
      have h₂ : 1 ≤ finrank K (negativeSquareKernel A (b : K)) :=
        Submodule.one_le_finrank_iff.mpr hV₂
      have hdimsum : finrank K (positiveSquareKernel A (b : K)) +
          finrank K (negativeSquareKernel A (b : K)) = finrank K V :=
        Submodule.finrank_add_eq_of_isCompl hcompl
      exact OmegaSmall.two_pow_nine_dvd_card_of_mulEquiv_orthogonalGroup_prod hK
        (omega_polarBilin_comp_nondeg hnd₁) (omega_polarBilin_comp_nondeg hnd₂) h₁ h₂
        (by rw [hdimsum]; exact hd) e
    · exact (omega_false_of_obstruction hO hD
        (omega_classII hf hK' Q hQ A c μ hsquare hsimP hnonscalar b hb hneg
          (by omega))).elim
  · rcases hsign with hpos | hneg
    · exact (omega_false_of_obstruction hO hD
        (omega_classIII hf hK' Q hQ A c μ hsquare hsimP hsqc hpos (by omega))).elim
    · exact (omega_false_of_obstruction hO hD
        (omega_classIV hf hK' Q hQ A c μ hsquare hsimP hsqc hneg (by omega))).elim

end Core

section XCore

variable {K : Type} [Field K] [Finite K]

theorem omega_X_core_two (hK : Nat.card K = 3) {d : ℕ} (hd : d = 7 ∨ d = 8)
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hrep : SemilinearRepresentation Q)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      4 * Nat.card (matrixProjectiveDerived Q))
    (hO : LieOrderFormulasInput) (σ : MulAut (matrixProjectiveDerived Q)) (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) :
    2 ^ 6 ∣ Nat.card ↥(fixedSubgroup σ) := by
  have hd0 : 0 < d := by omega
  have hσ2 : σ * σ = 1 := by
    have h := pow_orderOf_eq_one σ
    rw [hσ] at h
    rwa [← pow_two]
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    omega
  obtain ⟨β, g, hg, hgσ2, ⟨c, hc⟩, hlin, hfield⟩ := hrep.2 σ hσ2 hσ1
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
  have hQ' : ∃ v, Q v ≠ 0 := exists_ne_zero_of_polarBilin_nondegenerate Q hQ hd0
  obtain ⟨D'', hD''⟩ := omega_a6Hyp_linear Q hQ' g hg1 hD'
  have hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) =
      (c : K) • x := by
    intro x
    have h := coordinateSemilinearMap_sq_apply g.val c (by rw [hg1, one_pow]) hc x
    rwa [coordinateSemilinearMap_eq_matrix g.val hg1] at h
  have hnonscalar := matrixLinearEquiv_ne_smul_one g.val.left (hlin hg1)
  have hfin : finrank K (Fin d → K) = d := Module.finrank_fin_fun K
  have hfinite : Finite (projectiveDerived Q) :=
    Finite.of_equiv _ (projectiveEquiv Q hQ').toEquiv
  have hC := omega_linear_core_two (V := Fin d → K) hK hO Q hQ (matrixLinearEquiv g.val.left) c
    (multiplier Q g) hsq (matrix_similarity Q g hg1) hnonscalar (by rw [hfin]; exact hd) hD''
  have hF := OmegaSmall.two_pow_sub_two_dvd_card_fixed_matrixProjectiveConjugation hd0 Q hQ g hg1
    hcard hC
  rw [hcongr]
  exact (pow_dvd_pow 2 (by norm_num : 6 ≤ 9 - 2)).trans hF

end XCore

end CFSG.ComponentClassification.CatFC

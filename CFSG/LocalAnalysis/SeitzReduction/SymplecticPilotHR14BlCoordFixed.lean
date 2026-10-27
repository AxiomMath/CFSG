module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlCoordShape

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_conj eichler_add_smul_self
  eichler_mem_elementaryGroup elementaryGroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (commSpace)

section Core

variable {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem bCoord_mem_span_omegaInvVec (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hdim : 2 ≤ finrank K (omegaInvSpace s)) {v : V} (hsv : s v = v)
    (hfix : ∀ u y : V, Q u = 0 → polar Q u y = 0 →
      eichler Q u y * s = s * eichler Q u y → eichler Q u y v = v) :
    v ∈ K ∙ omegaInvVec hQ hs hss := by
  set w₀ := omegaInvVec hQ hs hss with hw₀
  have hvperp : ∀ w' ∈ omegaInvSpace s, polar Q v w' = 0 :=
    (omegaInvNil_eq_zero_iff hQ hs hss).1 (omegaInvNil_eq_zero_iff_apply.2 hsv)
  have hstep : ∀ a : V, polar Q a w₀ = 0 → omegaInvNil s a ≠ 0 → polar Q v a = 0 := by
    intro a ha hNa
    have hlam : omegaInvLambda hs hss a = 0 := by rw [← polar_omegaInvVec hQ hs hss a, ← hw₀, ha]
    have hu : Q (omegaInvNil s a) = 0 := by
      rw [← omegaInvLambda_sq hs hss, hlam, zero_pow two_ne_zero]
    have huy : polar Q (omegaInvNil s a) a = 0 := by
      rw [polar_comm, ← map_omegaInvNil hs, hu]
    have hsa : s a = a + (1 : K) • omegaInvNil s a := by
      rw [one_smul, omegaInvNil_apply]
      abel
    have hcomm : eichler Q (omegaInvNil s a) a * s = s * eichler Q (omegaInvNil s a) a := by
      have h1 := eichler_conj hs (omegaInvNil s a) a
      rw [apply_omegaInvNil hss, hsa, eichler_add_smul_self hu] at h1
      calc eichler Q (omegaInvNil s a) a * s =
          (s * eichler Q (omegaInvNil s a) a * s⁻¹) * s := by rw [h1]
        _ = s * eichler Q (omegaInvNil s a) a := by group
    have h2 := hfix _ a hu huy hcomm
    rw [eichler_apply hu huy, hvperp _ (omegaInvNil_mem_omegaInvSpace s a), zero_smul, add_zero,
      mul_zero, add_zero, sub_eq_self, smul_eq_zero] at h2
    exact h2.resolve_right hNa
  have hex : ∃ a'' : V, polar Q a'' w₀ = 0 ∧ omegaInvNil s a'' ≠ 0 := by
    by_contra hne
    push Not at hne
    have hle : omegaInvSpace s ≤ K ∙ w₀ := by
      intro x hx
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ omegaInv_polarBilin_isRefl (K ∙ w₀),
        LinearMap.BilinForm.mem_orthogonal_iff]
      intro a ha
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at ha
      have haw : polar Q a w₀ = 0 := by
        rw [polar_comm, ← polarBilin_apply_apply]
        exact ha w₀ (Submodule.mem_span_singleton_self w₀)
      have hNa := hne a haw
      rw [polarBilin_apply_apply]
      exact (omegaInvNil_eq_zero_iff hQ hs hss).1 hNa x hx
    have h1 := Submodule.finrank_mono hle
    have h2 : finrank K (K ∙ w₀) ≤ 1 :=
      (finrank_span_le_card ({w₀} : Set V)).trans (by simp)
    omega
  obtain ⟨a'', ha''w, ha''N⟩ := hex
  have hall : ∀ a : V, polar Q a w₀ = 0 → polar Q v a = 0 := by
    intro a ha
    by_cases hNa : omegaInvNil s a = 0
    · have h1 : polar Q (a + a'') w₀ = 0 := by rw [polar_add_left, ha, ha''w, add_zero]
      have h2 : omegaInvNil s (a + a'') ≠ 0 := by rwa [map_add, hNa, zero_add]
      have h3 := hstep _ h1 h2
      rw [polar_add_right, hstep a'' ha''w ha''N, add_zero] at h3
      exact h3
    · exact hstep a ha hNa
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ omegaInv_polarBilin_isRefl (K ∙ w₀),
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro a ha
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at ha
  have haw : polar Q a w₀ = 0 := by
    rw [polar_comm, ← polarBilin_apply_apply]
    exact ha w₀ (Submodule.mem_span_singleton_self w₀)
  rw [polarBilin_apply_apply, polar_comm]
  exact hall a haw

end Core

theorem omegaBFixedVectorInput_holds : OmegaBFixedVectorInput := by
  intro n K _ _ _ Q hQ hT hE s hs j hj hrank w hw hfixw v hsv hfixv
  have hS : matrixLinearIso s.val ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have hSS := bCoord_mul_self_linear hs
  have hdim : 2 ≤ finrank K (omegaInvSpace (matrixLinearIso s.val)) := by
    change 2 ≤ finrank K (commSpace (matrixLinearIso s.val))
    rw [hrank]
    omega
  have hcore : ∀ x : Fin (2 * (n + 1)) → K, matrixLinearIso s.val x = x →
      (∀ g ∈ matrixDerived Q, g * s.val = s.val * g →
        (g : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K) *ᵥ x = x) →
      x ∈ K ∙ omegaInvVec hQ hS hSS := by
    intro x hx hgx
    refine bCoord_mem_span_omegaInvVec hQ hS hSS hdim hx fun u y hu huy hcomm => ?_
    have hmem : matrixLinearIso.symm (eichler Q u y) ∈ matrixDerived Q := by
      rw [CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.mem_matrixDerived_iff,
        MulEquiv.apply_symm_apply, hE]
      exact eichler_mem_elementaryGroup Q u y
    have hc : matrixLinearIso.symm (eichler Q u y) * s.val =
        s.val * matrixLinearIso.symm (eichler Q u y) := by
      apply matrixLinearIso.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hcomm
    have h1 := hgx _ hmem hc
    rw [← CFSG.RankThree.PartOne.AUTSL.matrixLinearIso_apply, MulEquiv.apply_symm_apply] at h1
    exact h1
  have hB : OmegaInvTypeB Q (matrixLinearIso s.val)
      (finrank K (omegaInvSpace (matrixLinearIso s.val))) := ⟨hS, hSS, rfl, by
        change Odd (finrank K (commSpace (matrixLinearIso s.val)))
        rw [hrank]
        exact ⟨j, rfl⟩⟩
  have hQw₀ : Q (omegaInvVec hQ hS hSS) = 1 := (omegaInvVec_typeB hQ hB).2.1
  have hw' : w ∈ K ∙ omegaInvVec hQ hS hSS :=
    hcore w (hfixw s.val s.2 rfl)
      (fun g hg hgs => hfixw g (matrixDerived_le_isometries Q hg) hgs)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hw'
  have hc1 : c = 1 := by
    have h3 := congrArg Q hc
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hQw₀, mul_one, hw, _root_.sq] at h3
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.eq_one_of_mul_self_eq_one_of_charTwo h3
  have hww₀ : omegaInvVec hQ hS hSS = w := by rw [← hc, hc1, one_smul]
  rw [← hww₀]
  exact hcore v hsv hfixv

theorem spOmegaBShapeInputCoord_of_param (hM1 : OmegaBSpParamInput) (κ : Sp2mKind) :
    SpOmegaBShapeInputCoord κ :=
  spOmegaBShapeInputCoord_of_model hM1 omegaBFixedVectorInput_holds κ

end CFSG.SeitzReduction.SymplecticPilot

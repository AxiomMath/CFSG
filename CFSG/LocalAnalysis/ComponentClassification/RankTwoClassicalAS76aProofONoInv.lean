module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOSiegel
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

section Commutant

variable {K : Type} [Field K] [Finite K] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem eq_smul_one_of_commute_statedOmega (hK : 2 < Nat.card K) (R : QuadraticForm K (κ → K))
    (hR : R.polarBilin.Nondegenerate) (hκ : 3 ≤ Fintype.card κ) {M : Matrix κ κ K}
    (h : ∀ Z ∈ StatedOmega ⇑R, M * (Z : Matrix κ κ K) = (Z : Matrix κ κ K) * M) :
    ∃ c : K, M = c • 1 := by
  have hdim : 3 ≤ Module.finrank K (κ → K) := by rwa [Module.finrank_fintype_fun_eq_card]
  obtain ⟨hiff, -⟩ :=
    CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar hK R hR
      hdim
  obtain ⟨c, hc⟩ := (hiff M.mulVecLin).mp fun g hg => by
    set Z := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv κ K).symm g
    have hZ : Z ∈ StatedOmega ⇑R := by
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap rfl, mem_comap]
      change CFSG.ClassicalGroups.Orthogonal.toLinEquiv κ K Z ∈ _
      rwa [MulEquiv.apply_symm_apply]
    have hgZ : ∀ v, g v = (Z : Matrix κ κ K) *ᵥ v := fun v => by
      rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, MulEquiv.apply_symm_apply]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply, hgZ,
      mulVec_mulVec, h Z hZ]
  refine ⟨c, Matrix.ext_iff_mulVec.mpr fun v => ?_⟩
  have h1 := congrArg (fun f : (κ → K) →ₗ[K] (κ → K) => f v) hc
  simp only [Matrix.mulVecLin_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
  rw [h1, smul_mulVec, one_mulVec]

end Commutant

section Matrices

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}

theorem eq_oblk_smul_of_commute {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {M : Matrix ι ι K}
    (h2 : ∀ A : SL(2, K), M * oblk oe 1 (rhoTwoMat A) = oblk oe 1 (rhoTwoMat A) * M)
    (h1 : ∀ B : SL(2, K), M * oblk oe 1 (rhoOneMat B) = oblk oe 1 (rhoOneMat B) * M) :
    ∃ (Y : Matrix ι₂ ι₂ K) (c : K), M = oblk oe Y (c • 1) := by
  obtain ⟨A₀, hA₀⟩ := exists_diag_sl2 ht0
  have ht1' : t⁻¹ ≠ 1 := fun h => ht1 (by rw [← inv_inv t, h, inv_one])
  have hH : IsUnit (rhoTwoMat A₀ - 1).det := by
    have hdiag : rhoTwoMat A₀ - 1 =
        diagonal (Sum.elim ![t - 1, t⁻¹ - 1] ![t⁻¹ - 1, t - 1]) := by
      rw [rhoTwoMat_apply, hA₀, adjugate_fin_two]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
    rw [hdiag, det_diagonal]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    rcases i with i | i <;> fin_cases i <;>
      simp [sub_ne_zero.mpr ht1, sub_ne_zero.mpr ht1']
  obtain ⟨Y, X, hYX⟩ := eq_oblk_of_commute hH (h2 A₀)
  have hX : ∀ H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      M * oblk oe 1 H = oblk oe 1 H * M → X * H = H * X := by
    intro H hgH
    rw [hYX, oblk_mul, oblk_mul, Matrix.mul_one, Matrix.one_mul] at hgH
    exact (oblk_injective hgH).2
  have hXc := eq_smul_one_of_commute_rho
    (hX _ (by rw [← rhoTwoMat_tr_zero_one]; exact h2 _))
    (hX _ (by rw [← rhoTwoMat_tr_one_zero]; exact h2 _))
    (hX _ (by rw [← rhoOneMat_tr_zero_one]; exact h1 _))
    (hX _ (by rw [← rhoOneMat_tr_one_zero]; exact h1 _))
  exact ⟨Y, _, by rw [hYX, ← hXc]⟩

theorem rhoTwoMat_slTr (a : K) :
    rhoTwoMat (slTr a) = 1 + a • fromBlocks (single 0 1 1) 0 0 (single 1 0 1) := by
  rw [rhoTwoMat_apply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  simp only [smul_zero, add_zero]
  congr 1
  · simp [slTr, smul_single]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [slTr, adjugate_fin_two, CharTwo.neg_eq]

end Matrices

section Fix

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤}
  {β : MulAut (StatedProj (StatedOmega Q))} {σ : K ≃+* K} {A : GL ι K}
  (hβ : ∀ g : StatedOmega Q, ∃ hg : A * glAut σ (g : GL ι K) * A⁻¹ ∈ StatedOmega Q,
    β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
  (hinj : Function.Injective (oProj Q))
include hβ hinj

omit [CharP K 2] in
theorem mul_glAut_eq_of_fix {g : StatedOmega Q} (hg : β (oProj Q g) = oProj Q g) :
    A * glAut σ (g : GL ι K) = (g : GL ι K) * A := by
  obtain ⟨hg', hβg⟩ := hβ g
  have h1 : oProj Q ⟨_, hg'⟩ = oProj Q g := hβg.symm.trans hg
  have h2 : A * glAut σ (g : GL ι K) * A⁻¹ = (g : GL ι K) := congrArg Subtype.val (hinj h1)
  calc A * glAut σ (g : GL ι K) = A * glAut σ (g : GL ι K) * A⁻¹ * A := by group
    _ = (g : GL ι K) * A := by rw [h2]

theorem refl_of_fixes_oBarTwo (hW : ∀ x ∈ oBarTwo oe hQ hSL, β x = x) : σ = RingEquiv.refl K := by
  set N : Matrix ι ι K := oblk oe 0 (fromBlocks (single 0 1 1) 0 0 (single 1 0 1)) with hN
  have hmat : ∀ a : K, ((oRhoTwo oe hQ hSL (slTr a) : GL ι K) : Matrix ι ι K) = 1 + a • N := by
    intro a
    rw [coe_oRhoTwo, rhoTwoMat_slTr, oblk_one_add_smul]
  have hNmap : N.map σ = N := by
    simp only [hN, oblk_map_fun _ (map_zero σ), fromBlocks_map, Matrix.map_zero _ (map_zero σ),
      map_single, map_one]
  have hkey : ∀ a : K, (A : Matrix ι ι K) * (1 + σ a • N) = (1 + a • N) * A := by
    intro a
    have h := mul_glAut_eq_of_fix hβ hinj (hW _ ⟨slTr a, rfl⟩)
    have h' := congrArg (fun x : GL ι K => (x : Matrix ι ι K)) h
    simp only [Units.val_mul, coe_glAut, hmat] at h'
    rwa [Matrix.map_add _ (map_add σ), Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.map_smul' _ _ _ (map_mul σ), hNmap] at h'
  have hAN : (A : Matrix ι ι K) * N = N * A := by
    have h := hkey 1
    rw [map_one, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  have hN0 : (A : Matrix ι ι K) * N ≠ 0 := by
    intro h0
    have h1 : N = 0 := by
      calc N = ((A⁻¹ : GL ι K) : Matrix ι ι K) * ((A : Matrix ι ι K) * N) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              Matrix.one_mul]
        _ = 0 := by rw [h0, Matrix.mul_zero]
    have h2 := congrFun (congrFun (congrArg (fun M : Matrix ι ι K =>
      (reindexAlgEquiv K K oe).symm M) h1) (.inr (.inl 0))) (.inr (.inl 1))
    simp [hN, oblk] at h2
  ext a
  have h := hkey a
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, ← hAN, add_right_inj] at h
  have h3 : (σ a - a) • ((A : Matrix ι ι K) * N) = 0 := by rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hN0)

end Fix

section Trivial

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤}

theorem eq_one_of_fixes_oBars (hinj : Function.Injective (oProj Q))
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {β : MulAut (StatedProj (StatedOmega Q))}
    {σ : K ≃+* K} {A : GL ι K} {μ : K}
    (hAQ : ∀ v, Q ((A : Matrix ι ι K) *ᵥ fun i => σ (v i)) = μ * σ (Q v))
    (hβ : ∀ g : StatedOmega Q, ∃ hg : A * glAut σ (g : GL ι K) * A⁻¹ ∈ StatedOmega Q,
      β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    (hW : ∀ x ∈ oBarTwo oe hQ hSL, β x = x) (hW₂ : ∀ x ∈ oBarOne oe hQ hSL, β x = x)
    (hL : ∀ x ∈ oBarL oe hQ, β x = x) : β = 1 := by
  obtain rfl := refl_of_fixes_oBarTwo hβ hinj hW
  have hfix : ∀ g : StatedOmega Q, β (oProj Q g) = oProj Q g →
      (A : Matrix ι ι K) * (g : GL ι K) = ((g : GL ι K) : Matrix ι ι K) * A := by
    intro g hg
    have h := congrArg (fun x : GL ι K => (x : Matrix ι ι K)) (mul_glAut_eq_of_fix hβ hinj hg)
    simp only [Units.val_mul, coe_glAut] at h
    rwa [show ((g : GL ι K) : Matrix ι ι K).map (RingEquiv.refl K) = (g : GL ι K) from
      Matrix.map_id _] at h
  obtain ⟨Y, c, hYc⟩ := eq_oblk_smul_of_commute (oe := oe) ht0 ht1
    (fun A' => by rw [← coe_oRhoTwo (hQ := hQ) (hSL := hSL)]; exact hfix _ (hW _ ⟨A', rfl⟩))
    (fun B => by rw [← coe_oRhoOne (hQ := hQ) (hSL := hSL)]; exact hfix _ (hW₂ _ ⟨B, rfl⟩))
  obtain ⟨d, hd⟩ := hcomm Y fun Z hZ => by
    have h := hfix (oKappa oe hQ ⟨Z, hZ⟩) (hL _ ⟨⟨Z, hZ⟩, rfl⟩)
    rw [coe_oKappa, hYc, oblk_mul, oblk_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact (oblk_injective h).1
  have hQ0 : Q₂ 0 = 0 := by simpa using hsm 0 w₀
  set u₁ : Fin 2 ⊕ Fin 2 → K := Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1
  have hu₁ : StatedQuadPlus 2 K u₁ = 1 := by simp [StatedQuadPlus, Fin.sum_univ_two, u₁]
  have hsm₁ : StatedQuadPlus 2 K (c • u₁) = c * c := by
    simp [StatedQuadPlus, Fin.sum_univ_two, u₁]
  have hA : ∀ v, (A : Matrix ι ι K) *ᵥ v = oVec oe (d • fun a => v (oe (.inl a)))
      (c • fun b => v (oe (.inr b))) := fun v => by
    rw [hYc, hd, oblk_mulVec_eq, smul_mulVec, smul_mulVec, one_mulVec, one_mulVec]
  have hμc : c * c = μ := by
    have h := hAQ (oVec oe 0 u₁)
    simp only [RingEquiv.refl_apply] at h
    rw [hA, hQ, hQ, oVec_inl, oVec_inr, oVec_inl, oVec_inr, smul_zero, hQ0, hu₁, zero_add,
      zero_add, mul_one] at h
    rwa [hsm₁] at h
  have hμd : d * d = μ := by
    have h := hAQ (oVec oe w₀ 0)
    simp only [RingEquiv.refl_apply] at h
    rw [hA, hQ, hQ, oVec_inl, oVec_inr, oVec_inl, oVec_inr, smul_zero, hsm,
      show StatedQuadPlus 2 K 0 = 0 by simp [StatedQuadPlus], add_zero, add_zero] at h
    exact mul_right_cancel₀ hw₀ h
  have hcd : c = d := by
    have h : (c + d) * (c + d) = 0 := by
      have e : (c + d) * (c + d) = c * c + d * d + 2 * (c * d) := by ring
      rw [e, CharTwo.two_eq_zero, zero_mul, add_zero, hμc, hμd, CharTwo.add_self_eq_zero]
    have h' : c + d = 0 := mul_self_eq_zero.mp h
    calc c = c + d + d := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = d := by rw [h', zero_add]
  have hAs : (A : Matrix ι ι K) = c • 1 := by
    rw [hYc, hd, hcd, ← oblk_smul, oblk_one]
  have hAcomm : ∀ X : GL ι K, A * X = X * A := fun X => Units.ext (by
    rw [Units.val_mul, Units.val_mul, hAs, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one])
  ext x
  obtain ⟨g, rfl⟩ := oProj_surjective Q x
  obtain ⟨hg, hβg⟩ := hβ g
  rw [MulAut.one_apply]
  change β (QuotientGroup.mk g) = _
  rw [hβg]
  congr 1
  apply Subtype.ext
  change A * glAut (RingEquiv.refl K) (g : GL ι K) * A⁻¹ = (g : GL ι K)
  rw [hAcomm, mul_inv_cancel_right]
  exact Units.ext (by rw [coe_glAut]; exact Matrix.map_id _)

end Trivial

end CFSG.ComponentClassification.RankTwoClassical

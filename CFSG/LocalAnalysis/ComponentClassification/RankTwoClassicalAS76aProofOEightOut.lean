module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightLayer

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

section Conj

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤}

theorem exists_eq_conj_oRhoOne (hinj : Function.Injective (oProj Q))
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {β : MulAut (StatedProj (StatedOmega Q))}
    {σ : K ≃+* K} {A : GL ι K} {μ : K} (hμ0 : μ ≠ 0)
    (hAQ : ∀ v, Q ((A : Matrix ι ι K) *ᵥ fun i => σ (v i)) = μ * σ (Q v))
    (hβ : ∀ g : StatedOmega Q, ∃ hg : A * glAut σ (g : GL ι K) * A⁻¹ ∈ StatedOmega Q,
      β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    (hW : ∀ x ∈ oBarTwo oe hQ hSL, β x = x) (hL : ∀ x ∈ oBarL oe hQ, β x = x) :
    ∃ B : SL(2, K), ∀ x, β x =
      oProj Q (oRhoOne oe hQ hSL B) * x * (oProj Q (oRhoOne oe hQ hSL B))⁻¹ := by
  obtain rfl := refl_of_fixes_oBarTwo hβ hinj hW
  have hfix : ∀ g : StatedOmega Q, β (oProj Q g) = oProj Q g →
      (A : Matrix ι ι K) * (g : GL ι K) = ((g : GL ι K) : Matrix ι ι K) * A := by
    intro g hg
    have h := congrArg (fun x : GL ι K => (x : Matrix ι ι K)) (mul_glAut_eq_of_fix hβ hinj hg)
    simp only [Units.val_mul, coe_glAut] at h
    rwa [show ((g : GL ι K) : Matrix ι ι K).map (RingEquiv.refl K) = (g : GL ι K) from
      Matrix.map_id _] at h
  obtain ⟨Y, B, hYB⟩ := eq_oblk_rhoOneShape_of_commute (oe := oe) ht0 ht1
    (fun A' => by rw [← coe_oRhoTwo (hQ := hQ) (hSL := hSL)]; exact hfix _ (hW _ ⟨A', rfl⟩))
  obtain ⟨d, hd⟩ := hcomm Y fun Z hZ => by
    have h := hfix (oKappa oe hQ ⟨Z, hZ⟩) (hL _ ⟨⟨Z, hZ⟩, rfl⟩)
    rw [coe_oKappa, hYB, oblk_mul, oblk_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact (oblk_injective h).1
  have hQ0 : Q₂ 0 = 0 := by simpa using hsm 0 w₀
  have hA : ∀ v, (A : Matrix ι ι K) *ᵥ v = oVec oe (d • fun a => v (oe (.inl a)))
      (rhoOneShape B *ᵥ fun b => v (oe (.inr b))) := fun v => by
    rw [hYB, hd, oblk_mulVec_eq, smul_mulVec, one_mulVec]
  have hμd : d * d = μ := by
    have h := hAQ (oVec oe w₀ 0)
    simp only [RingEquiv.refl_apply] at h
    rw [hA, hQ, hQ, oVec_inl, oVec_inr, oVec_inl, oVec_inr, Matrix.mulVec_zero, hsm,
      show StatedQuadPlus 2 K 0 = 0 by simp [StatedQuadPlus], add_zero, add_zero] at h
    exact mul_right_cancel₀ hw₀ h
  set u₁ : Fin 2 ⊕ Fin 2 → K := Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1
  have hu₁ : StatedQuadPlus 2 K u₁ = 1 := by simp [StatedQuadPlus, Fin.sum_univ_two, u₁]
  have hμB : B.det = μ := by
    have h := hAQ (oVec oe 0 u₁)
    simp only [RingEquiv.refl_apply] at h
    rw [hA, hQ, hQ, oVec_inl, oVec_inr, oVec_inl, oVec_inr, smul_zero, hQ0, zero_add, zero_add,
      quadPlus_two_rhoOneShape, hu₁, mul_one, mul_one] at h
    exact h
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hμ0 (by rw [← hμd, mul_zero])
  have hdet : (d⁻¹ • B).det = 1 := by
    rw [det_smul, Fintype.card_fin, hμB, ← hμd, inv_pow, sq, inv_mul_cancel₀ (mul_ne_zero hd0 hd0)]
  refine ⟨⟨d⁻¹ • B, hdet⟩, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := oProj_surjective Q x
  obtain ⟨hg, hβg⟩ := hβ g
  have hAR : A = Matrix.GeneralLinearGroup.scalar ι (Units.mk0 d hd0) *
      oRhoOneGL oe (⟨d⁻¹ • B, hdet⟩ : SL(2, K)) := by
    apply Units.ext
    change (A : Matrix ι ι K) = scalar ι d * oblk oe 1 (rhoOneShape (d⁻¹ • B))
    rw [hYB, hd, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      oblk_smul, rhoOneShape_smul, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  have hc : Matrix.GeneralLinearGroup.scalar ι (Units.mk0 d hd0) ∈ center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have hcent : ∀ M : GL ι K, A * M * A⁻¹ = oRhoOneGL oe (⟨d⁻¹ • B, hdet⟩ : SL(2, K)) * M *
      (oRhoOneGL oe (⟨d⁻¹ • B, hdet⟩ : SL(2, K)))⁻¹ := fun M => by
    rw [hAR, _root_.mul_inv_rev]
    set c := Matrix.GeneralLinearGroup.scalar ι (Units.mk0 d hd0)
    set R := oRhoOneGL oe (⟨d⁻¹ • B, hdet⟩ : SL(2, K))
    rw [show c * R * M * (R⁻¹ * c⁻¹) = c * (R * M * R⁻¹) * c⁻¹ by group,
      ← Subgroup.mem_center_iff.mp hc (R * M * R⁻¹), mul_inv_cancel_right]
  change β (QuotientGroup.mk g) = _
  rw [hβg]
  change oProj Q ⟨_, hg⟩ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change A * glAut (RingEquiv.refl K) (g : GL ι K) * A⁻¹ =
    oRhoOneGL oe (⟨d⁻¹ • B, hdet⟩ : SL(2, K)) * (g : GL ι K) *
      (oRhoOneGL oe (⟨d⁻¹ • B, hdet⟩ : SL(2, K)))⁻¹
  rw [show glAut (RingEquiv.refl K) (g : GL ι K) = g from
    Units.ext (by rw [coe_glAut]; exact Matrix.map_id _), hcent]

end Conj

section Lift

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂]
  [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}
  {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedOmega Q)}

omit [Finite K] in
theorem outerFree_oEight (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hinj : Function.Injective (oProj Q))
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hperf : commutator (StatedOmega Q₂) = ⊤)
    (hsemi : ∀ β : MulAut (StatedProj (StatedOmega Q)), (∀ x ∈ oBarTwo oe hQ hSL, β x = x) →
      (∀ x ∈ oBarL oe hQ, β x = x) → ∃ (σ : K ≃+* K) (A' : GL ι K) (μ : K), μ ≠ 0 ∧
        (∀ v, Q ((A' : Matrix ι ι K) *ᵥ fun i => σ (v i)) = μ * σ (Q v)) ∧
        ∀ g : StatedOmega Q, ∃ hg : A' * glAut σ (g : GL ι K) * A'⁻¹ ∈ StatedOmega Q,
          β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    (σ : MulAut ↥A)
    (hfix : ∀ y : ↥A, (y : G) ∈ levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarL oe hQ) →
      σ y = y) :
    ∃ l ∈ levLift θ (oBarOne oe hQ hSL), ∀ z : ↥A, (z : G) ∈ levLift θ (oBarOne oe hQ hSL) →
      ((σ z : ↥A) : G) = l * z * l⁻¹ := by
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hW := inducedAut_fix_of_levLift hθ commutator_oBarTwo le_sup_left hfix hα
  have hL := inducedAut_fix_of_levLift hθ (commutator_oBarL hperf) le_sup_right hfix hα
  obtain ⟨σ', A', μ, hμ0, hAQ, hβ⟩ := hsemi α hW hL
  obtain ⟨B, hB⟩ := exists_eq_conj_oRhoOne hinj hcomm hsm hw₀ ht0 ht1 hμ0 hAQ hβ hW hL
  exact exists_inner_levLift_of hker hθ commutator_oBarOne σ hα ⟨B, rfl⟩ fun x _ => hB x

omit [Finite K] in
theorem noInv_oEight (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hinj : Function.Injective (oProj Q))
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hperf : commutator (StatedOmega Q₂) = ⊤)
    (hsemi : ∀ β : MulAut (StatedProj (StatedOmega Q)), (∀ x ∈ oBarTwo oe hQ hSL, β x = x) →
      (∀ x ∈ oBarL oe hQ, β x = x) → ∃ (σ : K ≃+* K) (A' : GL ι K) (μ : K), μ ≠ 0 ∧
        (∀ v, Q ((A' : Matrix ι ι K) *ᵥ fun i => σ (v i)) = μ * σ (Q v)) ∧
        ∀ g : StatedOmega Q, ∃ hg : A' * glAut σ (g : GL ι K) * A'⁻¹ ∈ StatedOmega Q,
          β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩) :
    NoInvolutoryCentralizing A (levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarL oe hQ) ⊔
      levLift θ (oBarOne oe hQ hSL)) := by
  rw [sup_right_comm]
  refine noInv_oLevi hA hker hθ hperf fun β _ hW hW₂ hL => ?_
  obtain ⟨σ', A', μ, -, hAQ, hβ⟩ := hsemi β hW hL
  exact eq_one_of_fixes_oBars hinj hcomm hsm hw₀ ht0 ht1 hAQ hβ hW hW₂ hL

end Lift

end CFSG.ComponentClassification.RankTwoClassical

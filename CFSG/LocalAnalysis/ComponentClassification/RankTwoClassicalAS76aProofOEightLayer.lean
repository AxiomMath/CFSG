module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOFour
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

section Matrices

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}

theorem eq_oblk_rhoOneShape_of_commute {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {M : Matrix ι ι K}
    (h2 : ∀ A : SL(2, K), M * oblk oe 1 (rhoTwoMat A) = oblk oe 1 (rhoTwoMat A) * M) :
    ∃ (Y : Matrix ι₂ ι₂ K) (B : Matrix (Fin 2) (Fin 2) K), M = oblk oe Y (rhoOneShape B) := by
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
  obtain ⟨B, hB⟩ := exists_rhoOneShape_of_commute
    (hX _ (by rw [← rhoTwoMat_tr_zero_one]; exact h2 _))
    (hX _ (by rw [← rhoTwoMat_tr_one_zero]; exact h2 _))
  exact ⟨Y, B, by rw [hYX, hB]⟩

end Matrices

section Centralizer

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤}

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem eq_one_of_quad_smul (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K}
    (hw₀ : Q₂ w₀ ≠ 0) {d : K} (hd : Q₂ (d • w₀) = Q₂ w₀) : d = 1 := by
  rw [hsm] at hd
  exact eq_of_mul_self_eq ((mul_right_cancel₀ hw₀ (hd.trans (one_mul _).symm)).trans
    (mul_one 1).symm)

theorem exists_oRhoOne_of_commute
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {g : StatedOmega Q}
    (h2 : ∀ A : SL(2, K), g * oRhoTwo oe hQ hSL A = oRhoTwo oe hQ hSL A * g)
    (hL : ∀ Z : StatedOmega Q₂, g * oKappa oe hQ Z = oKappa oe hQ Z * g) :
    ∃ B : SL(2, K), g = oRhoOne oe hQ hSL B := by
  have hm2 : ∀ A : SL(2, K), (g : GL ι K).val * oblk oe 1 (rhoTwoMat A) =
      oblk oe 1 (rhoTwoMat A) * (g : GL ι K).val := fun A => by
    have := congrArg (fun x : StatedOmega Q => ((x : GL ι K) : Matrix ι ι K)) (h2 A)
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_oRhoTwo] using this
  obtain ⟨Y, B, hYB⟩ := eq_oblk_rhoOneShape_of_commute ht0 ht1 hm2
  obtain ⟨d, hd⟩ := hcomm Y fun Z hZ => by
    have h := congrArg (fun x : StatedOmega Q => ((x : GL ι K) : Matrix ι ι K)) (hL ⟨Z, hZ⟩)
    simp only [Subgroup.coe_mul, Units.val_mul, coe_oKappa] at h
    rw [hYB, oblk_mul, oblk_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact (oblk_injective h).1
  have hiso := quad_mulVec_of_mem_statedOmega g.2
  have hQ0 : Q₂ 0 = 0 := by simpa using hsm 0 w₀
  have hd1 : d = 1 := by
    refine eq_one_of_quad_smul hsm hw₀ ?_
    have h := hiso (oVec oe w₀ 0)
    rw [hYB, hd, quad_oblk_mulVec hQ, oVec_inl, oVec_inr, hQ, oVec_inl, oVec_inr,
      Matrix.mulVec_zero, smul_mulVec, Matrix.one_mulVec, add_left_inj] at h
    exact h
  set u₁ : Fin 2 ⊕ Fin 2 → K := Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1
  have hu₁ : StatedQuadPlus 2 K u₁ = 1 := by simp [StatedQuadPlus, Fin.sum_univ_two, u₁]
  have hdetB : B.det = 1 := by
    have h := hiso (oVec oe 0 u₁)
    rw [hYB, quad_oblk_mulVec hQ, oVec_inl, oVec_inr, hQ, oVec_inl, oVec_inr,
      Matrix.mulVec_zero, hQ0, zero_add, zero_add, quadPlus_two_rhoOneShape, hu₁, mul_one] at h
    exact h
  refine ⟨⟨B, hdetB⟩, Subtype.ext (Units.ext ?_)⟩
  change (g : GL ι K).val = oblk oe 1 (rhoOneMat ⟨B, hdetB⟩)
  rw [hYB, hd, hd1, one_smul]
  rfl

end Centralizer

section Layer

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂]
  [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}
  {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedOmega Q)}

@[expose] noncomputable def oBarOneEquiv (hinj : Function.Injective (oProj Q)) :
    SL(2, K) ≃* oBarOne oe hQ hSL :=
  MonoidHom.ofInjective (hinj.comp oRhoOne_injective)

omit [Finite K] in
theorem oBarTwo_sup_oBarL_le_centralizer :
    oBarTwo oe hQ hSL ⊔ oBarL oe hQ ≤
      centralizer (oBarOne oe hQ hSL : Set (StatedProj (StatedOmega Q))) :=
  sup_le (fun _ hx => mem_centralizer_iff.mpr fun _ hy => (oBarOne_commute_oBarTwo hy hx))
    (fun _ hx => mem_centralizer_iff.mpr fun _ hy => (oBarOne_commute_oBarL hy hx))

omit [Finite K] in
theorem oLeviY_four_le :
    levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarL oe hQ) ≤
      liftSub θ (centralizer (oBarOne oe hQ hSL : Set (StatedProj (StatedOmega Q)))) :=
  sup_le (levLift_le_liftSub.trans (liftSub_mono (le_sup_left.trans
      oBarTwo_sup_oBarL_le_centralizer)))
    (levLift_le_liftSub.trans (liftSub_mono (le_sup_right.trans
      oBarTwo_sup_oBarL_le_centralizer)))

theorem isQuasisimple_oBarOne (hK : 4 ≤ Nat.card K) (hinj : Function.Injective (oProj Q)) :
    CFSG.IsQuasisimple ↥(oBarOne oe hQ hSL) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (oBarOneEquiv hinj)
    (CFSG.RankThree.Classical.isQuasisimple_SL2 (exists_finset_four hK))

theorem layerCentralizer_eq_oLeviW₂ (hK : 4 ≤ Nat.card K) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hinj : Function.Injective (oProj Q))
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hperf : commutator (StatedOmega Q₂) = ⊤) :
    AS76b.layerCentralizer A (levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarL oe hQ)) =
      levLift θ (oBarOne oe hQ hSL) := by
  set Y := levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarL oe hQ)
  have hmem : ∀ m ∈ A ⊓ centralizer (Y : Set G), ∀ hm : m ∈ A,
      θ ⟨m, hm⟩ ∈ oBarOne oe hQ hSL := by
    intro m hmM hm
    obtain ⟨g, hg⟩ := oProj_surjective Q (θ ⟨m, hm⟩)
    have hc : ∀ S : Subgroup (StatedProj (StatedOmega Q)), ⁅S, S⁆ = S → levLift θ S ≤ Y →
        ∀ x ∈ S, θ ⟨m, hm⟩ * x = x * θ ⟨m, hm⟩ := by
      intro S hS hSY x hx
      obtain ⟨w', hw', rfl⟩ := exists_mem_levLift hθ hS hx
      have h1 := (mem_centralizer_iff.mp (mem_inf.mp hmM).2 w' (hSY hw')).symm
      rw [← map_mul, ← map_mul]
      exact congrArg θ (Subtype.ext h1)
    obtain ⟨B, hB⟩ := exists_oRhoOne_of_commute (hQ := hQ) (hSL := hSL) hcomm hsm hw₀ ht0 ht1
      (g := g) (fun A' => hinj (by
        rw [map_mul, map_mul, hg]
        exact hc _ commutator_oBarTwo le_sup_left _ ⟨A', rfl⟩))
      (fun Z => hinj (by
        rw [map_mul, map_mul, hg]
        exact hc _ (commutator_oBarL hperf) le_sup_right _ ⟨Z, rfl⟩))
    exact ⟨B, by rw [← hg, hB]; rfl⟩
  refine layerCentralizer_eq_levLift hker hθ commutator_oBarOne (isQuasisimple_oBarOne hK hinj)
    ?_ (fun m hmM hm => (oBarOne oe hQ hSL).le_normalizer (hmem m hmM hm))
    (fun a ha b hb haA hbA => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hmem a ha haA) (hmem b hb hbA)) (inv_mem (hmem a ha haA)))
        (inv_mem (hmem b hb hbA)))
  refine le_inf levLift_le ?_
  rw [le_centralizer_iff]
  intro y hy
  obtain ⟨hyA, hyθ⟩ := mem_liftSub.mp (oLeviY_four_le hy)
  have := levLift_le_centralizer hker hyA (S := oBarOne oe hQ hSL)
    fun l hl => (mem_centralizer_iff.mp hyθ l hl).symm
  intro l hl
  exact mem_centralizer_singleton_iff.mp (this hl)

end Layer

end CFSG.ComponentClassification.RankTwoClassical

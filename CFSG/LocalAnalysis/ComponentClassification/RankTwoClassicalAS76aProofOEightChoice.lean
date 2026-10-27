module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSym
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSym
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

section Choice

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂]
  [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}
  {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤} {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedOmega Q)}

omit [Finite K] in
theorem center_oBarOne_eq_bot (hinj : Function.Injective (oProj Q)) :
    center ↥(oBarOne oe hQ hSL) = ⊥ := by
  rw [← Subgroup.map_center_eq (oBarOneEquiv hinj), center_SL2_eq_bot', Subgroup.map_bot]

omit [Finite K] in
theorem odd_card_center_oLeviW₂ (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hZ : Odd (Nat.card (center ↥A))) (hinj : Function.Injective (oProj Q)) :
    Odd (Nat.card (center ↥(levLift θ (oBarOne oe hQ hSL)))) :=
  odd_card_center_levLift hker hθ commutator_oBarOne hZ
    (by rw [center_oBarOne_eq_bot hinj, Subgroup.card_bot]; exact odd_one)

omit [Finite G] in
theorem statedClassicalModel_oLeviW₂ {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hinj : Function.Injective (oProj Q)) :
    StatedClassicalModel (rankTwoQuot (levLift θ (oBarOne oe hQ hSL))) .PSL 2 2 m := by
  have hq : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩, K, inferInstance,
    inferInstance, hK, ⟨((levLiftQuotEquiv hker hθ commutator_oBarOne).trans
      (QuotientGroup.congr (center (oBarOne oe hQ hSL)) (center SL(2, K))
        (oBarOneEquiv hinj).symm (Subgroup.map_center_eq _))).trans
          (projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩
  · simp only [Prod.mk.injEq] at h
    omega
  · simp only [Prod.mk.injEq] at h
    omega

theorem sym_oEight (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hZ : Odd (Nat.card (center ↥A))) {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) (hinj : Function.Injective (oProj Q))
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
    {ω : K} (hω : ω * ω + ω + 1 = 0) (hω0 : ω ≠ 0) {s₂ : GL ι₂ K} (hs₂ : s₂ * s₂ = 1)
    (hiso₂ : ∀ w, Q₂ ((s₂ : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w) {s₀ : StatedOmega Q}
    (hs₀ : (s₀ : GL ι K) = oblkGL oe (s₂, swapOneGL)) :
    ∃ (D' : Subgroup G) (s x : G),
      levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarL oe hQ) =
        D' ⊔ levLift θ (oBarTwo oe hQ hSL) ∧ s ∈ A ∧
      rightConjugate (levLift θ (oBarTwo oe hQ hSL)) s = levLift θ (oBarOne oe hQ hSL) ∧
      rightConjugate (levLift θ (oBarOne oe hQ hSL)) s = levLift θ (oBarTwo oe hQ hSL) ∧
      rightConjugate D' s = D' ∧ x ∈ levLift θ (oBarOne oe hQ hSL) ∧ orderOf x = 5 ∧
      AS76b.layerCentralizer A (D' ⊔ zpowers x) = levLift θ (oBarTwo oe hQ hSL) ∧
      NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ levLift θ (oBarTwo oe hQ hSL)) := by
  have hK4 := four_le_card hK hm
  obtain ⟨sA, hsA⟩ := hθ (oProj Q s₀)
  have hsθ : (θ ⟨(sA : G), sA.2⟩)⁻¹ = oProj Q s₀ := by
    rw [show (⟨(sA : G), sA.2⟩ : ↥A) = sA from rfl, hsA, ← map_inv, swap_inv hs₂ hs₀]
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hxL, hxA, hxθ, hx5⟩ := exists_mem_levLift_orderOf hker hθ hZ hm hK
    commutator_oBarOne (oBarOneEquiv hinj) (s := oProj Q (oRhoOne oe hQ hSL (fiveSL ω)))
    ⟨fiveSL ω, rfl⟩ (by rw [← map_pow, ← map_pow, fiveSL_pow_five hω, map_one, map_one])
    (fun h => fiveSL_ne_one ω ((hinj.comp oRhoOne_injective) (by
      simp only [Function.comp_apply, map_one]
      exact h)))
  refine ⟨levLift θ (oBarL oe hQ), sA, x, sup_comm _ _, sA.2, ?_, ?_, ?_, hxL, hx5,
    layerCentralizer_eq_oLeviW_five hK4 hker hθ hinj hcomm hsm hw₀ hperf hω0 hxL hxA hxθ,
    noInv_oEight_five hA hker hθ hinj hcomm hsm hw₀ ht0 ht1 hperf hsemi hω0 hxA hxθ⟩
  · rw [rightConjugate_levLift sA.2, hsθ, map_conj_oBarTwo_swap hs₂ hs₀]
  · rw [rightConjugate_levLift sA.2, hsθ, map_conj_oBarOne_swap hs₂ hs₀]
  · rw [rightConjugate_levLift sA.2, hsθ, map_conj_oBarL_swap hs₂ hs₀ hiso₂]

theorem leviChoice_orth_four_of {m : ℕ} (hm2 : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (hA : commutator ↥A = ⊤) (hZ : Odd (Nat.card (center ↥A))) (hker : θ.ker = center ↥A)
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
          β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    {D : ClassicalModel A} {p : G} (hq : D.q = 2 ^ m) {T : Set G} (hαD : D.alpha p = closure T)
    (hT : ∀ y ∈ T, y ∈ liftSub θ (oBarOne oe hQ hSL) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1)
    (hlevi : D.LeviType (levLift θ (oBarOne oe hQ hSL))) (h5 : ¬ D.IsLinearFiveFour)
    (hsym : D.IsLTwoFour → ∃ (D' : Subgroup G) (s x : G),
      levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarL oe hQ) =
        D' ⊔ levLift θ (oBarTwo oe hQ hSL) ∧ s ∈ A ∧
      rightConjugate (levLift θ (oBarTwo oe hQ hSL)) s = levLift θ (oBarOne oe hQ hSL) ∧
      rightConjugate (levLift θ (oBarOne oe hQ hSL)) s = levLift θ (oBarTwo oe hQ hSL) ∧
      rightConjugate D' s = D' ∧ x ∈ levLift θ (oBarOne oe hQ hSL) ∧ orderOf x = 5 ∧
      AS76b.layerCentralizer A (D' ⊔ zpowers x) = levLift θ (oBarTwo oe hQ hSL) ∧
      NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ levLift θ (oBarTwo oe hQ hSL))) :
    LeviChoice D p (levLift θ (oBarTwo oe hQ hSL))
      (levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarL oe hQ)) := by
  have hK4 := four_le_card hK hm2
  have hlayer := layerCentralizer_eq_oLeviW₂ (θ := θ) (oe := oe) (hQ := hQ) (hSL := hSL) hK4 hker
    hθ hinj hcomm hsm hw₀ ht0 ht1 hperf
  refine
    { W_le := le_sup_left
      Y_le := ?_
      W_type := ⟨K, inferInstance, inferInstance, by rw [hK, hq],
        nonempty_oLeviW_equiv hm2 hK hker hθ hZ hinj⟩
      alpha_le := ?_
      quasisimple := ?_
      oddCenter := ?_
      levi := ?_
      noInv := ?_
      diag := fun h => (h5 h).elim
      outerFree := ?_
      sym := ?_ }
  · rw [hαD]
    refine le_inf ((oLeviY_four_le).trans liftSub_le)
      (le_centralizer_closure_levLift hker hZ hT fun x hx => ?_)
    obtain ⟨hxA, hxθ⟩ := mem_liftSub.mp (oLeviY_four_le hx)
    exact ⟨hxA, fun l hl => (mem_centralizer_iff.mp hxθ l hl).symm⟩
  · rw [hαD, hlayer]
    exact closure_le_levLift hker hθ commutator_oBarOne hZ hT
  · rw [hlayer]
    obtain ⟨hp, hs, -⟩ := isQuasisimple_levLift hker hθ
      (commutator_oBarOne (oe := oe) (hQ := hQ) (hSL := hSL)) (isQuasisimple_oBarOne hK4 hinj)
    exact ⟨hp.commutator_eq_top, hs⟩
  · rw [hlayer]
    exact odd_card_center_oLeviW₂ hker hθ hZ hinj
  · rw [hlayer]
    exact hlevi
  · rw [hlayer]
    exact noInv_oEight hA hker hθ hinj hcomm hsm hw₀ ht0 ht1 hperf hsemi
  · rw [hlayer]
    exact fun _ σ _ hfix => outerFree_oEight hker hθ hinj hcomm hsm hw₀ ht0 ht1 hperf hsemi σ hfix
  · rw [hlayer]
    exact hsym

end Choice

end CFSG.ComponentClassification.RankTwoClassical

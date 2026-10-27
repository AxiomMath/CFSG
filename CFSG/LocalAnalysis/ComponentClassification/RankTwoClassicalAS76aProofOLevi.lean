module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviNoInv
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOLayer

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

section Bars

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤}

@[expose] noncomputable def oBarTwoEquiv (hinj : Function.Injective (oProj Q)) :
    SL(2, K) ≃* oBarTwo oe hQ hSL :=
  MonoidHom.ofInjective (hinj.comp oRhoTwo_injective)

@[expose] noncomputable def oBarLEquiv (hinj : Function.Injective (oProj Q)) :
    StatedOmega Q₂ ≃* oBarL oe hQ :=
  MonoidHom.ofInjective (hinj.comp oKappa_injective)

omit [CharP K 2] in
theorem commutator_oBarTwo : ⁅oBarTwo oe hQ hSL, oBarTwo oe hQ hSL⁆ = oBarTwo oe hQ hSL :=
  commutator_range_of_perfect _ hSL

theorem commutator_oBarOne : ⁅oBarOne oe hQ hSL, oBarOne oe hQ hSL⁆ = oBarOne oe hQ hSL :=
  commutator_range_of_perfect _ hSL

omit [CharP K 2] in
theorem commutator_oBarL (hperf : commutator (StatedOmega Q₂) = ⊤) :
    ⁅oBarL oe hQ, oBarL oe hQ⁆ = oBarL oe hQ :=
  commutator_range_of_perfect _ hperf

omit [CharP K 2] in
theorem oBarTwo_le_centralizer_oBarL :
    oBarTwo oe hQ hSL ≤ centralizer (oBarL oe hQ : Set (StatedProj (StatedOmega Q))) :=
  fun _ hx => mem_centralizer_iff.mpr fun _ hy => (oBarTwo_commute_oBarL hx hy).symm

theorem oBarOne_le_centralizer_oBarL :
    oBarOne oe hQ hSL ≤ centralizer (oBarL oe hQ : Set (StatedProj (StatedOmega Q))) :=
  fun _ hx => mem_centralizer_iff.mpr fun _ hy => (oBarOne_commute_oBarL hx hy).symm

end Bars

section Levi

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedOmega Q)}

theorem oLevi_Y_le :
    levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarOne oe hQ hSL) ≤
      liftSub θ (centralizer (oBarL oe hQ : Set (StatedProj (StatedOmega Q)))) :=
  sup_le (levLift_le_liftSub.trans (liftSub_mono oBarTwo_le_centralizer_oBarL))
    (levLift_le_liftSub.trans (liftSub_mono oBarOne_le_centralizer_oBarL))

omit [CharP K 2] in
theorem oLeviL_le_centralizer (hker : θ.ker = center ↥A) {Y : Subgroup G}
    (hY : Y ≤ liftSub θ (centralizer (oBarL oe hQ : Set (StatedProj (StatedOmega Q))))) :
    levLift θ (oBarL oe hQ) ≤ A ⊓ centralizer (Y : Set G) := by
  refine le_inf levLift_le ?_
  rw [le_centralizer_iff]
  intro y hy
  obtain ⟨hyA, hyθ⟩ := mem_liftSub.mp (hY hy)
  have := levLift_le_centralizer hker hyA (S := oBarL oe hQ)
    fun l hl => (mem_centralizer_iff.mp hyθ l hl).symm
  intro l hl
  exact mem_centralizer_singleton_iff.mp (this hl)

omit [CharP K 2] in
theorem isQuasisimple_oBarL (hinj : Function.Injective (oProj Q))
    (hqs : CFSG.IsQuasisimple (StatedOmega Q₂)) : CFSG.IsQuasisimple ↥(oBarL oe hQ) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (oBarLEquiv hinj) hqs

theorem layerCentralizer_eq_oLeviL_of_le (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hinj : Function.Injective (oProj Q)) {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (hperf : commutator (StatedOmega Q₂) = ⊤)
    (hqs : CFSG.IsQuasisimple (StatedOmega Q₂)) {Y : Subgroup G}
    (hWY : levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarOne oe hQ hSL) ≤ Y)
    (hY : Y ≤ liftSub θ (centralizer (oBarL oe hQ : Set (StatedProj (StatedOmega Q))))) :
    AS76b.layerCentralizer A Y = levLift θ (oBarL oe hQ) :=
  layerCentralizer_eq_oLeviL hker hθ hinj ht0 ht1 (commutator_oBarL hperf)
    (isQuasisimple_oBarL hinj hqs) (le_sup_left.trans hWY) (le_sup_right.trans hWY)
    (oLeviL_le_centralizer hker hY)

omit [CharP K 2] in
theorem oLevi_Y_le_centralizer (hker : θ.ker = center ↥A) (hZ : Odd (Nat.card (center ↥A)))
    {T : Set G} (hT : ∀ y ∈ T, y ∈ liftSub θ (oBarL oe hQ) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1)
    {Y : Subgroup G}
    (hY : Y ≤ liftSub θ (centralizer (oBarL oe hQ : Set (StatedProj (StatedOmega Q))))) :
    Y ≤ A ⊓ centralizer (closure T : Set G) := by
  refine le_inf (hY.trans liftSub_le) (le_centralizer_closure_levLift hker hZ hT fun x hx => ?_)
  obtain ⟨hxA, hxθ⟩ := mem_liftSub.mp (hY hx)
  exact ⟨hxA, fun l hl => (mem_centralizer_iff.mp hxθ l hl).symm⟩

omit [CharP K 2] in
theorem oLevi_alpha_le [Finite G] (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hZ : Odd (Nat.card (center ↥A))) (hperf : commutator (StatedOmega Q₂) = ⊤) {T : Set G}
    (hT : ∀ y ∈ T, y ∈ liftSub θ (oBarL oe hQ) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1) :
    closure T ≤ levLift θ (oBarL oe hQ) :=
  closure_le_levLift hker hθ (commutator_oBarL hperf) hZ hT

omit [CharP K 2] in
theorem nonempty_oLeviW_equiv [Finite G] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hZ : Odd (Nat.card (center ↥A))) (hinj : Function.Injective (oProj Q)) :
    Nonempty (↥(levLift θ (oBarTwo oe hQ hSL)) ≃* SL(2, K)) :=
  nonempty_levLift_equiv_SL2 hker hθ hZ hm hK commutator_oBarTwo (oBarTwoEquiv hinj)

omit [CharP K 2] in
theorem isQuasisimple_oLeviL (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hinj : Function.Injective (oProj Q)) (hperf : commutator (StatedOmega Q₂) = ⊤)
    (hqs : CFSG.IsQuasisimple (StatedOmega Q₂)) :
    CFSG.Open.IsQuasisimple ↥(levLift θ (oBarL oe hQ)) := by
  obtain ⟨hp, hs, -⟩ := isQuasisimple_levLift hker hθ (commutator_oBarL hperf)
    (isQuasisimple_oBarL hinj hqs)
  exact ⟨hp.commutator_eq_top, hs⟩

omit [CharP K 2] in
theorem odd_card_center_oLeviL [Finite G] (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hZ : Odd (Nat.card (center ↥A)))
    (hinj : Function.Injective (oProj Q)) (hperf : commutator (StatedOmega Q₂) = ⊤)
    (hZ₂ : Odd (Nat.card (center (StatedOmega Q₂)))) :
    Odd (Nat.card (center ↥(levLift θ (oBarL oe hQ)))) :=
  odd_card_center_levLift hker hθ (commutator_oBarL hperf) hZ
    (by rw [← card_center_congr (oBarLEquiv hinj)]; exact hZ₂)

omit [CharP K 2] in
@[expose] noncomputable def oLeviLQuotEquiv (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hinj : Function.Injective (oProj Q))
    (hperf : commutator (StatedOmega Q₂) = ⊤) :
    rankTwoQuot (levLift θ (oBarL oe hQ)) ≃* StatedOmega Q₂ ⧸ center (StatedOmega Q₂) :=
  (levLiftQuotEquiv hker hθ (commutator_oBarL hperf)).trans
    (QuotientGroup.congr (center (oBarL oe hQ)) (center (StatedOmega Q₂))
      (oBarLEquiv hinj).symm (Subgroup.map_center_eq _))

theorem noInv_oLevi (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hperf : commutator (StatedOmega Q₂) = ⊤)
    (h : ∀ β : MulAut (StatedProj (StatedOmega Q)), β * β = 1 →
      (∀ x ∈ oBarTwo oe hQ hSL, β x = x) → (∀ x ∈ oBarOne oe hQ hSL, β x = x) →
        (∀ x ∈ oBarL oe hQ, β x = x) → β = 1) :
    NoInvolutoryCentralizing A (levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarOne oe hQ hSL) ⊔
      levLift θ (oBarL oe hQ)) := by
  intro σ hσ hfix
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hW := inducedAut_fix_of_levLift hθ commutator_oBarTwo (le_sup_left.trans le_sup_left)
    hfix hα
  have hW₂ := inducedAut_fix_of_levLift hθ commutator_oBarOne (le_sup_right.trans le_sup_left)
    hfix hα
  have hL := inducedAut_fix_of_levLift hθ (commutator_oBarL hperf) le_sup_right hfix hα
  have h1 := h α (inducedAut_sq hθ hσ hα) hW hW₂ hL
  exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

end Levi

end CFSG.ComponentClassification.RankTwoClassical

module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapTriangle

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam AgreeOn FlipOn)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section FirstFactor

variable {G : Type*} [Group G] {t : G} {D D' : Subgroup G}

theorem exists_twist_agreeOn_of_dichotomy (ht2 : t * t = 1) {P : SwapParam t D}
    {P' : SwapParam t D'} {O : Subgroup G} (h : AgreeOn P P' O ∨ FlipOn P P' O) :
    ∃ s : ℤˣ, AgreeOn P (P'.twist s) O := by
  refine ⟨SeitzQ2.agreeSign P P' O, fun x hx => ?_⟩
  rw [SeitzQ2.SwapParam.lft_twist, SeitzQ2.twistOn_agreeSign h x hx, ← SeitzQ2.signConj_mul ht2,
    Int.units_mul_self, SeitzQ2.signConj_one]

theorem not_commute_lft_of_injective (P : SwapParam t D) (hinj : Function.Injective P.Ψ)
    {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hxy : ¬Commute x y) :
    ¬Commute (P.lft x) (P.lft y) := by
  intro h
  apply hxy
  rw [P.lft_of_mem hx, P.lft_of_mem hy] at h
  have h1 : P.Ψ ((⟨x, hx⟩, 1) * (⟨y, hy⟩, 1)) = P.Ψ ((⟨y, hy⟩, 1) * (⟨x, hx⟩, 1)) := by
    rw [map_mul, map_mul]
    exact h.eq
  have h2 : ((⟨x, hx⟩ : D) * ⟨y, hy⟩ : D) = ⟨y, hy⟩ * ⟨x, hx⟩ := congrArg Prod.fst (hinj h1)
  exact congrArg Subtype.val h2

theorem agreeOn_of_pentagon {D₂ D₃ D₄ D₅ : Subgroup G} {P₂ : SwapParam t D₂}
    {P₃ : SwapParam t D₃} {P₄ : SwapParam t D₄} {P₅ : SwapParam t D₅} {O₂₃ O₃₅ O₄₅ : Subgroup G}
    {a b c : G} (h₂₃ : AgreeOn P₂ P₃ O₂₃ ∨ FlipOn P₂ P₃ O₂₃)
    (h₃₅ : AgreeOn P₃ P₅ O₃₅ ∨ FlipOn P₃ P₅ O₃₅) (h₄₅ : AgreeOn P₄ P₅ O₄₅) (ha₂₃ : a ∈ O₂₃)
    (ha₃₅ : a ∈ O₃₅) (ha₄₅ : a ∈ O₄₅) (hb : P₄.lft b = P₂.lft b) (hc : P₄.lft c = P₃.lft c)
    (hab : ¬Commute (P₄.lft a) (P₄.lft b)) (hac : ¬Commute (P₄.lft a) (P₄.lft c)) :
    AgreeOn P₂ P₃ O₂₃ := by
  have h4a : P₅.lft a = P₄.lft a := h₄₅ a ha₄₅
  rcases h₃₅ with h₃₅ | h₃₅
  · rcases h₂₃ with h₂₃ | h₂₃
    · exact h₂₃
    · refine absurd ?_ hab
      rw [← h4a, h₃₅ a ha₃₅, h₂₃ a ha₂₃, hb]
      exact (P₂.commute_lft_conj_lft b a).symm
  · refine absurd ?_ hac
    rw [← h4a, h₃₅ a ha₃₅, hc]
    exact (P₃.commute_lft_conj_lft c a).symm

end FirstFactor

section Triangle

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

@[expose] def swapParamTriple {D₁ D₂ D₃ : Subgroup G} (P₁ : SwapParam t D₁)
    (P₂ : SwapParam t D₂) (P₃ : SwapParam t D₃) : ∀ k : Fin 3, SwapParam t (![D₁, D₂, D₃] k)
  | ⟨0, _⟩ => P₁
  | ⟨1, _⟩ => P₂
  | ⟨2, _⟩ => P₃

theorem false_of_coherent_triangle {P : Type} [Group P] [Finite P] (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P) (hP : SeitzQ2.SwapPairExclusion P)
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X₁ X₂ X₃ D₁ D₂ D₃ : Subgroup G} (P₁ : SwapParam t D₁) (P₂ : SwapParam t D₂)
    (P₃ : SwapParam t D₃) (hinj₁ : Function.Injective P₁.Ψ) (hinj₂ : Function.Injective P₂.Ψ)
    (hinj₃ : Function.Injective P₃.Ψ) (hrange₁ : P₁.Ψ.range = centralizerPerfectCore X₁)
    (hrange₂ : P₂.Ψ.range = centralizerPerfectCore X₂)
    (hrange₃ : P₃.Ψ.range = centralizerPerfectCore X₃)
    (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L) (hX₃L : X₃ ≤ L)
    (h₂₁ : X₂ ≤ D₁) (h₃₁ : X₃ ≤ D₁) (h₁₂ : X₁ ≤ D₂) (h₃₂ : X₃ ≤ D₂) (h₁₃ : X₁ ≤ D₃)
    (h₂₃ : X₂ ≤ D₃)
    (a₁₂ : AgreeOn P₁ P₂ (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))))
    (a₁₃ : AgreeOn P₁ P₃ (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))))
    (a₂₃ : AgreeOn P₂ P₃ (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))))
    (hgen : perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) ⊔
      perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) ⊔
        perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) = L) : False := by
  have e₂₁ : perfectCore (D₂ ⊓ centralizer (X₁ : Set G)) =
      perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) := by
    rw [P₂.perfectCore_inf_centralizer_eq hinj₂ hrange₂ h₁₂,
      P₁.perfectCore_inf_centralizer_eq hinj₁ hrange₁ h₂₁, sup_comm]
  have e₃₁ : perfectCore (D₃ ⊓ centralizer (X₁ : Set G)) =
      perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) := by
    rw [P₃.perfectCore_inf_centralizer_eq hinj₃ hrange₃ h₁₃,
      P₁.perfectCore_inf_centralizer_eq hinj₁ hrange₁ h₃₁, sup_comm]
  have e₃₂ : perfectCore (D₃ ⊓ centralizer (X₂ : Set G)) =
      perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) := by
    rw [P₃.perfectCore_inf_centralizer_eq hinj₃ hrange₃ h₂₃,
      P₂.perfectCore_inf_centralizer_eq hinj₂ hrange₂ h₃₂, sup_comm]
  set O₁₂ := perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) with hO₁₂
  set O₁₃ := perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) with hO₁₃
  set O₂₃ := perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) with hO₂₃
  have hO₁₂D₁ : O₁₂ ≤ D₁ := (perfectCore_le _).trans inf_le_left
  have hO₁₃D₁ : O₁₃ ≤ D₁ := (perfectCore_le _).trans inf_le_left
  have hO₂₃D₂ : O₂₃ ≤ D₂ := (perfectCore_le _).trans inf_le_left
  have hO₁₂D₂ : O₁₂ ≤ D₂ := e₂₁ ▸ (perfectCore_le _).trans inf_le_left
  have hO₁₃D₃ : O₁₃ ≤ D₃ := e₃₁ ▸ (perfectCore_le _).trans inf_le_left
  have hO₂₃D₃ : O₂₃ ≤ D₃ := e₃₂ ▸ (perfectCore_le _).trans inf_le_left
  have hD₁ := E8Pilot.swapParam_le_centralizer P₁ hrange₁
  have hD₂ := E8Pilot.swapParam_le_centralizer P₂ hrange₂
  have hcen : ∀ {O A B : Subgroup G}, O ≤ centralizer (A : Set G) →
      O ≤ centralizer (B : Set G) → O ≤ centralizer ((A ⊔ B : Subgroup G) : Set G) :=
    fun hA hB => le_centralizer_iff.2 (sup_le (le_centralizer_iff.1 hA) (le_centralizer_iff.1 hB))
  refine SeitzQ2.false_of_coherent_swapParam_of_swapPairExclusion hset hOut e hP ht hKt
    (swapParamTriple P₁ P₂ P₃) ![O₁₂, O₁₃, O₂₃] ![0, 0, 1] (fun k => ?_) (fun k => ?_)
    (fun k l => ?_) ?_ ![X₁ ⊔ X₂, X₁ ⊔ X₃, X₂ ⊔ X₃] (fun k => ?_) (fun k => ?_) (fun k => ?_)
  · fin_cases k
    · exact hO₁₂D₁
    · exact hO₁₃D₁
    · exact hO₂₃D₂
  · fin_cases k <;> exact perfectCore_perfect _
  · fin_cases k <;> fin_cases l
    · exact ⟨0, hO₁₂D₁, hO₁₂D₁, AgreeOn.refl _ _, AgreeOn.refl _ _⟩
    · exact ⟨0, hO₁₂D₁, hO₁₃D₁, AgreeOn.refl _ _, AgreeOn.refl _ _⟩
    · exact ⟨1, hO₁₂D₂, hO₂₃D₂, a₁₂, AgreeOn.refl _ _⟩
    · exact ⟨0, hO₁₃D₁, hO₁₂D₁, AgreeOn.refl _ _, AgreeOn.refl _ _⟩
    · exact ⟨0, hO₁₃D₁, hO₁₃D₁, AgreeOn.refl _ _, AgreeOn.refl _ _⟩
    · exact ⟨2, hO₁₃D₃, hO₂₃D₃, a₁₃, a₂₃⟩
    · exact ⟨1, hO₂₃D₂, hO₁₂D₂, AgreeOn.refl _ _, a₁₂⟩
    · exact ⟨2, hO₂₃D₃, hO₁₃D₃, a₂₃, a₁₃⟩
    · exact ⟨1, hO₂₃D₂, hO₂₃D₂, AgreeOn.refl _ _, AgreeOn.refl _ _⟩
  · rw [E8Pilot.iSup_fin_three_subgroup]
    exact hgen
  · fin_cases k
    · exact sup_le hX₁L hX₂L
    · exact sup_le hX₁L hX₃L
    · exact sup_le hX₂L hX₃L
  · fin_cases k
    · exact hcen (hO₁₂D₁.trans hD₁) ((perfectCore_le _).trans inf_le_right)
    · exact hcen (hO₁₃D₁.trans hD₁) ((perfectCore_le _).trans inf_le_right)
    · exact hcen (hO₂₃D₂.trans hD₂) ((perfectCore_le _).trans inf_le_right)
  · fin_cases k
    · exact P₁.centralizerPerfectCore_sup_eq hinj₁ hrange₁ h₂₁
    · exact P₁.centralizerPerfectCore_sup_eq hinj₁ hrange₁ h₃₁
    · exact P₂.centralizerPerfectCore_sup_eq hinj₂ hrange₂ h₃₂

end Triangle

section Pentagon

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem false_of_swapParam_pentagon {P : Type} [Group P] [Finite P] (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P) (hP : SeitzQ2.SwapPairExclusion P)
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X₁ X₂ X₃ X₄ X₅ D₁ D₂ D₃ D₄ D₅ : Subgroup G} (P₁ : SwapParam t D₁) (P₂ : SwapParam t D₂)
    (P₃ : SwapParam t D₃) (P₄ : SwapParam t D₄) (P₅ : SwapParam t D₅)
    (hinj₁ : Function.Injective P₁.Ψ) (hinj₂ : Function.Injective P₂.Ψ)
    (hinj₃ : Function.Injective P₃.Ψ) (hinj₄ : Function.Injective P₄.Ψ)
    (hinj₅ : Function.Injective P₅.Ψ) (hrange₁ : P₁.Ψ.range = centralizerPerfectCore X₁)
    (hrange₂ : P₂.Ψ.range = centralizerPerfectCore X₂)
    (hrange₃ : P₃.Ψ.range = centralizerPerfectCore X₃)
    (hrange₄ : P₄.Ψ.range = centralizerPerfectCore X₄)
    (hrange₅ : P₅.Ψ.range = centralizerPerfectCore X₅)
    (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L) (hX₃L : X₃ ≤ L)
    (h₂₁ : X₂ ≤ D₁) (h₃₁ : X₃ ≤ D₁) (h₁₂ : X₁ ≤ D₂) (h₃₂ : X₃ ≤ D₂) (h₁₃ : X₁ ≤ D₃)
    (h₂₃ : X₂ ≤ D₃) (h₄₁ : X₄ ≤ D₁) (h₁₄ : X₁ ≤ D₄) (h₅₃ : X₅ ≤ D₃) (h₃₅ : X₃ ≤ D₅)
    (h₅₄ : X₅ ≤ D₄) (h₄₅ : X₄ ≤ D₅)
    (hS₁₂ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))))
    (hS₁₃ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))))
    (hS₂₃ : IsSimpleGroup (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))))
    (hS₁₄ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₄ : Set G))))
    (hS₃₅ : IsSimpleGroup (perfectCore (D₃ ⊓ centralizer (X₅ : Set G))))
    (hS₄₅ : IsSimpleGroup (perfectCore (D₄ ⊓ centralizer (X₅ : Set G))))
    (hZ₁₂ : center (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))) = ⊥)
    (hZ₁₃ : center (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))) = ⊥)
    (hZ₂₃ : center (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))) = ⊥)
    (hZ₁₄ : center (perfectCore (D₁ ⊓ centralizer (X₄ : Set G))) = ⊥)
    (hZ₃₅ : center (perfectCore (D₃ ⊓ centralizer (X₅ : Set G))) = ⊥)
    (hZ₄₅ : center (perfectCore (D₄ ⊓ centralizer (X₅ : Set G))) = ⊥)
    {a b c : G} (hb₁₂ : b ∈ perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))
    (hb₁₄ : b ∈ perfectCore (D₁ ⊓ centralizer (X₄ : Set G)))
    (hc₁₃ : c ∈ perfectCore (D₁ ⊓ centralizer (X₃ : Set G)))
    (hc₁₄ : c ∈ perfectCore (D₁ ⊓ centralizer (X₄ : Set G)))
    (ha₂₃ : a ∈ perfectCore (D₂ ⊓ centralizer (X₃ : Set G)))
    (ha₃₅ : a ∈ perfectCore (D₃ ⊓ centralizer (X₅ : Set G)))
    (ha₄₅ : a ∈ perfectCore (D₄ ⊓ centralizer (X₅ : Set G))) (hab : ¬Commute a b)
    (hac : ¬Commute a c)
    (hgen : perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) ⊔
      perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) ⊔
        perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) = L) : False := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨-, d₁₂⟩ := by
    haveI := hS₁₂
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours P₁ P₂ hinj₁ hinj₂ hrange₁ hrange₂ h₂₁ h₁₂ hZ₁₂
  obtain ⟨-, d₁₃⟩ := by
    haveI := hS₁₃
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours P₁ P₃ hinj₁ hinj₃ hrange₁ hrange₃ h₃₁ h₁₃ hZ₁₃
  obtain ⟨e₄₁, d₁₄⟩ := by
    haveI := hS₁₄
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours P₁ P₄ hinj₁ hinj₄ hrange₁ hrange₄ h₄₁ h₁₄ hZ₁₄
  obtain ⟨s₂, a₁₂⟩ := exists_twist_agreeOn_of_dichotomy htt d₁₂
  obtain ⟨s₃, a₁₃⟩ := exists_twist_agreeOn_of_dichotomy htt d₁₃
  obtain ⟨s₄, a₁₄⟩ := exists_twist_agreeOn_of_dichotomy htt d₁₄
  have hinj₂' := E8Pilot.swapParam_twist_injective P₂ hinj₂ s₂
  have hinj₃' := E8Pilot.swapParam_twist_injective P₃ hinj₃ s₃
  have hinj₄' := E8Pilot.swapParam_twist_injective P₄ hinj₄ s₄
  have hrange₂' := (E8Pilot.swapParam_twist_range P₂ s₂).trans hrange₂
  have hrange₃' := (E8Pilot.swapParam_twist_range P₃ s₃).trans hrange₃
  have hrange₄' := (E8Pilot.swapParam_twist_range P₄ s₄).trans hrange₄
  obtain ⟨-, d₄₅⟩ := by
    haveI := hS₄₅
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours (P₄.twist s₄) P₅ hinj₄' hinj₅ hrange₄' hrange₅
      h₅₄ h₄₅ hZ₄₅
  obtain ⟨s₅, a₄₅⟩ := exists_twist_agreeOn_of_dichotomy htt d₄₅
  have hinj₅' := E8Pilot.swapParam_twist_injective P₅ hinj₅ s₅
  have hrange₅' := (E8Pilot.swapParam_twist_range P₅ s₅).trans hrange₅
  obtain ⟨-, d₂₃⟩ := by
    haveI := hS₂₃
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours (P₂.twist s₂) (P₃.twist s₃) hinj₂' hinj₃'
      hrange₂' hrange₃' h₃₂ h₂₃ hZ₂₃
  obtain ⟨-, d₃₅⟩ := by
    haveI := hS₃₅
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours (P₃.twist s₃) (P₅.twist s₅) hinj₃' hinj₅'
      hrange₃' hrange₅' h₅₃ h₃₅ hZ₃₅
  have haD₄ : a ∈ D₄ := (mem_inf.1 (perfectCore_le _ ha₄₅)).1
  have hbD₄ : b ∈ D₄ := by
    rw [← e₄₁] at hb₁₄
    exact (mem_inf.1 (perfectCore_le _ hb₁₄)).1
  have hcD₄ : c ∈ D₄ := by
    rw [← e₄₁] at hc₁₄
    exact (mem_inf.1 (perfectCore_le _ hc₁₄)).1
  have a₂₃ := agreeOn_of_pentagon d₂₃ d₃₅ a₄₅ ha₂₃ ha₃₅ ha₄₅
    ((a₁₄ b hb₁₄).trans (a₁₂ b hb₁₂).symm) ((a₁₄ c hc₁₄).trans (a₁₃ c hc₁₃).symm)
    (not_commute_lft_of_injective _ hinj₄' haD₄ hbD₄ hab)
    (not_commute_lft_of_injective _ hinj₄' haD₄ hcD₄ hac)
  exact false_of_coherent_triangle hset hOut e hP ht hKt P₁ (P₂.twist s₂) (P₃.twist s₃) hinj₁
    hinj₂' hinj₃' hrange₁ hrange₂' hrange₃' hX₁L hX₂L hX₃L h₂₁ h₃₁ h₁₂ h₃₂ h₁₃ h₂₃ a₁₂ a₁₃ a₂₃
    hgen

end Pentagon

end CFSG.SeitzReduction.LinearPilot

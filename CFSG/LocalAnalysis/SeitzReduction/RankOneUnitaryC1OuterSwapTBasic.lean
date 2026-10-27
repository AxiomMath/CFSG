module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterNormSwap
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterSwapTAbel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

@[expose] def swapS₂ {G : Type} [Group G] (P U T : Subgroup G) : Subgroup G :=
  P ⊓ normalizer ((U ⊔ T : Subgroup G) : Set G)

theorem mem_swapS₂ {G : Type} [Group G] {P U T : Subgroup G} {g : G} :
    g ∈ swapS₂ P U T ↔ g ∈ P ∧ g ∈ normalizer ((U ⊔ T : Subgroup G) : Set G) :=
  mem_inf

structure U3C1OuterSwapTwo (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T R₂ D : Subgroup G) (d : G) (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G) : Prop where
  step : U3C1OuterStepHyp G L f t T R₂ D d V 1
  level : U3C1OuterLevelData G L f t T D V U U₁ 1
  mu : ¬ U₁ ≤ centralizer (V : Set G)
  idx : ∀ s ∈ T, ∀ s' ∈ T, s ∉ szT₁ L T ⊔ zpowers t → s' ∉ szT₁ L T ⊔ zpowers t →
    s * s'⁻¹ ∈ szT₁ L T ⊔ zpowers t
  w_mem : w ∈ T
  w_sq : w ^ 2 = 1
  w_not_mem : w ∉ szT₁ L T ⊔ zpowers t
  w_cent : ∀ r ∈ V, w * r * w⁻¹ = r
  isPGroup : IsPGroup 2 P
  le : U ⊔ T ≤ P
  s_mem_normalizer : s ∈ normalizer ((U ⊔ T : Subgroup G) : Set G)
  s_mem : s ∈ P
  conj_t : s * t * s⁻¹ = w
  conj_w : s * w * s⁻¹ = t
  conj_s_U₁ : ∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁

namespace U3C1OuterSwapTwo

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapTwo G L f t T R₂ D d V U U₁ w s P)
include hW

theorem t_mem : t ∈ T := (hW.step.start.start_of_card_sylow hW.step.card_sylow).1

theorem T₁_le_U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hW.level.sup_le_U₁

theorem wt_comm : w * t = t * w := mem_centralizer_singleton_iff.mp (hW.step.start.le hW.w_mem)

theorem le_S₂ : U ⊔ T ≤ swapS₂ P U T := le_inf hW.le Subgroup.le_normalizer

theorem s_mem_S₂ : s ∈ swapS₂ P U T := mem_swapS₂.mpr ⟨hW.s_mem, hW.s_mem_normalizer⟩

theorem isPGroup_S₂ : IsPGroup 2 (swapS₂ P U T) := hW.isPGroup.to_le inf_le_left

theorem swap_facts : s ∉ U ⊔ T ∧ s ^ 2 ∈ T ∧ s * (t * w) * s⁻¹ = t * w ∧
    ∀ g ∈ normalizer ((U ⊔ T : Subgroup G) : Set G), g ∈ P → g ∈ U ⊔ T ∨ g * s⁻¹ ∈ U ⊔ T :=
  hW.level.norm_swap_facts hW.step hW.mu hW.w_mem hW.w_sq hW.w_not_mem hW.w_cent hW.isPGroup
    hW.le hW.s_mem_normalizer hW.s_mem hW.conj_t hW.conj_w

theorem mem_or {g : G} (hg : g ∈ swapS₂ P U T) : g ∈ U ⊔ T ∨ g * s⁻¹ ∈ U ⊔ T :=
  hW.swap_facts.2.2.2 g (mem_swapS₂.mp hg).2 (mem_swapS₂.mp hg).1

theorem conj_U₁ {g : G} (hg : g ∈ swapS₂ P U T) {u : G} (hu : u ∈ U₁) : g * u * g⁻¹ ∈ U₁ := by
  have hSN := hW.level.muOne_sup_le_normalizer hW.step
  rcases hW.mem_or hg with h1 | h1
  · exact (mem_normalizer_iff.mp (hSN h1) u).mp hu
  · rw [show g * u * g⁻¹ = (g * s⁻¹) * (s * u * s⁻¹) * (g * s⁻¹)⁻¹ by group]
    exact (mem_normalizer_iff.mp (hSN h1) _).mp (hW.conj_s_U₁ u hu)

theorem not_mem_U₁_of_mem_T {z : G} (hzT : z ∈ T) (hz : z ∉ szT₁ L T) : z ∉ U₁ := fun h' =>
  hz (hW.level.muOne_mem_T₁_of_mem_T hW.step h' hzT)

theorem tw_not_mem_T₁ : t * w ∉ szT₁ L T := fun h' => hW.w_not_mem (by
  rw [show w = t⁻¹ * (t * w) by group]
  exact mul_mem (inv_mem (mem_sup_right (mem_zpowers t))) (mem_sup_left h'))

theorem t_mul_w_inv_not_mem_T₁ : t * w⁻¹ ∉ szT₁ L T := fun h' => hW.w_not_mem (by
  rw [show w = (t * w⁻¹)⁻¹ * t by group]
  exact mul_mem (inv_mem (mem_sup_left h')) (mem_sup_right (mem_zpowers t)))

theorem mem_U₁_cases {h : G} (hh : h ∈ U ⊔ T) :
    h ∈ U₁ ∨ h * t⁻¹ ∈ U₁ ∨ h * w⁻¹ ∈ U₁ ∨ h * (t * w)⁻¹ ∈ U₁ := by
  have hS := hW.step
  have hL := hW.level
  have hTU₁ : ∀ x ∈ T, ∀ u ∈ U₁, x * u * x⁻¹ ∈ U₁ := fun x hx u hu =>
    (mem_normalizer_iff.mp (hL.T_le hx) u).mp hu
  rw [hL.muOne_sup_eq hS] at hh
  obtain ⟨x, hx, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hL.T_le hh
  have key : ∀ z : G, z ∈ T → x * z⁻¹ ∈ szT₁ L T ⊔ zpowers t →
      (x * u * z⁻¹ ∈ U₁ ∨ x * u * (t * z)⁻¹ ∈ U₁) := by
    intro z hz hxz
    obtain ⟨y, hy, e, he, hye⟩ := exists_mul_eq_of_mem_sup_zpowers
      hS.start.mem_centralizer_szT₁ hxz
    rcases mem_zpowers_involution_eq_one_or_eq hS.start.sq_eq_one he with he1 | he1
    · left
      rw [he1, mul_one] at hye
      rw [show x * u * z⁻¹ = (x * z⁻¹) * (z * u * z⁻¹) by group, ← hye]
      exact mul_mem (hW.T₁_le_U₁ hy) (hTU₁ z hz u hu)
    · right
      rw [he1] at hye
      have e1 : x * u * (t * z)⁻¹ = (x * z⁻¹ * t⁻¹) * ((t * z) * u * (t * z)⁻¹) := by group
      rw [e1, ← hye, show y * t * t⁻¹ = y by group]
      exact mul_mem (hW.T₁_le_U₁ hy) (hTU₁ _ (mul_mem hW.t_mem hz) u hu)
  by_cases hxH : x ∈ szT₁ L T ⊔ zpowers t
  · rcases key 1 (one_mem _) (by simpa using hxH) with h1 | h1
    · left; simpa using h1
    · right; left; simpa using h1
  · have h1 := hW.idx x hx w hW.w_mem hxH hW.w_not_mem
    rcases key w hW.w_mem h1 with h2 | h2
    · right; right; left; exact h2
    · right; right; right; exact h2

theorem conj_of_not_mem {g : G} (hg : g ∈ swapS₂ P U T) (hgS : g ∉ U ⊔ T) :
    g * t * g⁻¹ * w⁻¹ ∈ U₁ ∧ g * w * g⁻¹ * t⁻¹ ∈ U₁ := by
  have hσ : g * s⁻¹ ∈ U ⊔ T := (hW.mem_or hg).resolve_left hgS
  have hcomm := hW.level.muOne_comm_mem_U₁ hW.step
  have hwS : w ∈ U ⊔ T := mem_sup_right hW.w_mem
  have htS : t ∈ U ⊔ T := mem_sup_right hW.t_mem
  constructor
  · have e : g * t * g⁻¹ * w⁻¹ = (g * s⁻¹) * w * (g * s⁻¹)⁻¹ * w⁻¹ := by
      rw [← hW.conj_t]; group
    rw [e]
    exact hcomm _ hσ _ hwS
  · have e : g * w * g⁻¹ * t⁻¹ = (g * s⁻¹) * t * (g * s⁻¹)⁻¹ * t⁻¹ := by
      rw [← hW.conj_w]; group
    rw [e]
    exact hcomm _ hσ _ htS

theorem card_T : Nat.card T = 4 * (2 ^ f) ^ 3 := by
  obtain ⟨hTK, hKcard⟩ := hW.step.start.swapT_card_eq_of_index_two hW.step.card_sylow hW.idx
    hW.w_mem hW.w_not_mem
  have hKT : (szT₁ L T ⊔ zpowers t) ⊔ zpowers w ≤ T :=
    sup_le (sup_le (szT₁_le_left L T) (zpowers_le.mpr hW.t_mem)) (zpowers_le.mpr hW.w_mem)
  have heq : (szT₁ L T ⊔ zpowers t) ⊔ zpowers w = T := le_antisymm hKT hTK
  rwa [heq] at hKcard

theorem U₁_inf_T : U₁ ⊓ T = szT₁ L T :=
  le_antisymm (fun _ hz => hW.level.muOne_mem_T₁_of_mem_T hW.step (mem_inf.mp hz).1
    (mem_inf.mp hz).2) (le_inf hW.T₁_le_U₁ (szT₁_le_left L T))

theorem card_SU : Nat.card (U ⊔ T : Subgroup G) = 4 * (2 ^ f) ^ 5 := by
  obtain ⟨hT₁card, -, -, -, -, -, -⟩ := hW.step.start.facts_of_card_sylow hW.step.card_sylow
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := U₁) (B := T) hW.level.T_le
  have hSU : U ⊔ T = U₁ ⊔ T := by rw [hW.level.muOne_sup_eq hW.step, sup_comm]
  rw [hW.U₁_inf_T, hT₁card, hW.level.muOne_card_U₁ hW.step, hW.card_T, ← hSU] at hprod
  have hq3 : 0 < (2 ^ f) ^ 3 := pow_pos (pow_pos (by norm_num) f) 3
  apply Nat.eq_of_mul_eq_mul_right hq3
  rw [hprod]
  ring

theorem relIndex_U₁_SU : U₁.relIndex (U ⊔ T) = 4 := by
  have h1 := relIndex_mul_card (H := U₁) (K := U ⊔ T)
  rw [inf_of_le_left (hW.level.U₁_le.trans le_sup_left), hW.level.muOne_card_U₁ hW.step,
    hW.card_SU] at h1
  have hq5 : 0 < (2 ^ f) ^ 5 := pow_pos (pow_pos (by norm_num) f) 5
  exact Nat.eq_of_mul_eq_mul_right hq5 h1

theorem relIndex_SU_S₂ : (U ⊔ T).relIndex (swapS₂ P U T) = 2 := by
  obtain ⟨hsS, hs2, -, -⟩ := hW.swap_facts
  rw [relIndex_eq_two_iff]
  refine ⟨s, hW.s_mem_S₂, fun b hb => ?_⟩
  by_cases hbS : b ∈ U ⊔ T
  · exact Or.inr ⟨hbS, fun h => hsS (by simpa using mul_mem (inv_mem hbS) h)⟩
  · refine Or.inl ⟨?_, hbS⟩
    have h1 := (hW.mem_or hb).resolve_left hbS
    rw [show b * s = (b * s⁻¹) * s ^ 2 by rw [sq]; group]
    exact mul_mem h1 (mem_sup_right hs2)

theorem relIndex_U₁_S₂ : U₁.relIndex (swapS₂ P U T) = 8 := by
  rw [← Subgroup.relIndex_mul_relIndex U₁ (U ⊔ T) (swapS₂ P U T)
    (hW.level.U₁_le.trans le_sup_left) hW.le_S₂, hW.relIndex_U₁_SU, hW.relIndex_SU_S₂]

theorem conj_mem_T_of_commute {c : G} (hcT : ∀ τ ∈ T, c * τ * c⁻¹ ∈ swapS₂ P U T) {z : G}
    (hz : z ∈ swapS₂ P U T) (hzx : z * (c * t * c⁻¹) = (c * t * c⁻¹) * z) :
    c⁻¹ * z * c ∈ T := by
  set P' : Subgroup G := (swapS₂ P U T).map (MulAut.conj c⁻¹).toMonoidHom with hP'
  have hP'2 : IsPGroup 2 P' := hW.isPGroup_S₂.map _
  have hmem : ∀ y ∈ swapS₂ P U T, c⁻¹ * y * c ∈ P' := fun y hy =>
    ⟨y, hy, by simp⟩
  have hTP' : T ≤ P' := fun τ hτ => by
    have := hmem _ (hcT τ hτ)
    rwa [show c⁻¹ * (c * τ * c⁻¹) * c = τ by group] at this
  refine U3C1OuterLevelData.norm_mem_T_of_commute hW.step hP'2 hTP' (hmem z hz) ?_
  calc c⁻¹ * z * c * t = c⁻¹ * (z * (c * t * c⁻¹)) * c := by group
    _ = c⁻¹ * ((c * t * c⁻¹) * z) * c := by rw [hzx]
    _ = t * (c⁻¹ * z * c) := by group

end U3C1OuterSwapTwo

end CFSG.SeitzReduction.RankOne

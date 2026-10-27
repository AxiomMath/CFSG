module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbDefs

public section

open Subgroup CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

theorem normalizer_R_le : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
  have hR1 : R ≠ ⊥ := fun h1 => by
    have := h.cardR
    rw [h1, card_bot] at this
    omega
  rw [← normalizer_centralizer_eq h.hyp.standard]
  exact normalizer_two_subgroup_le _ _ (tightlyEmbedded_centralizer h.hyp.standard)
    h.sylowR.isPGroup h.sylowR.le hR1

variable {P : Subgroup G} {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

theorem outer_mem_normalizer_A : x ∈ normalizer (A : Set G) := h.normalizer_R_le hx.normR

theorem outer_not_inner : ¬ ∃ a ∈ A, ∀ y ∈ A, x * y * x⁻¹ = a * y * a⁻¹ := by
  rintro ⟨a, haA, hax⟩
  obtain ⟨eA⟩ := h.equiv
  obtain ⟨b₀, -, hb₀N, -, hb₀tr, hb₀norm⟩ := exists_klein_three eA h.V₀_le_A h.card_V₀
  have hxV₀ : x ∈ normalizer (V₀ : Set G) := h.normalizer_le_normalizer_V₀ hx.normV
  have haN : a ∈ normalizer (V₀ : Set G) := by
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [← hax w (h.V₀_le_A hw)]
      exact (mem_normalizer_iff.mp hxV₀ w).mp hw
    · intro hw
      have hwA : w ∈ A := by
        have h1 := mul_mem (mul_mem (inv_mem haA) (h.V₀_le_A hw)) haA
        rwa [show a⁻¹ * (a * w * a⁻¹) * a = w by group] at h1
      rw [← hax w hwA] at hw
      exact (mem_normalizer_iff.mp hxV₀ w).mpr hw
  obtain ⟨v, hv, b, hb, rfl⟩ :=
    AS76b.exists_mul_of_mem_sup_of_le_normalizer (zpowers_le.mpr hb₀N) (hb₀norm _ haA haN)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
  have hact : ∀ w ∈ V₀, x * w * x⁻¹ = b₀ ^ k * w * (b₀ ^ k)⁻¹ := by
    intro w hw
    have hbw : b₀ ^ k * w * (b₀ ^ k)⁻¹ ∈ V₀ :=
      (mem_normalizer_iff.mp (zpow_mem hb₀N k) w).mp hw
    rw [hax w (h.V₀_le_A hw)]
    calc v * b₀ ^ k * w * (v * b₀ ^ k)⁻¹ = v * (b₀ ^ k * w * (b₀ ^ k)⁻¹) * v⁻¹ := by group
      _ = b₀ ^ k * w * (b₀ ^ k)⁻¹ * v * v⁻¹ := by
          rw [h.comm (h.V₀_le hv) (h.V₀_le hbw)]
      _ = b₀ ^ k * w * (b₀ ^ k)⁻¹ := by group
  have hz : b₀ ^ k * z * (b₀ ^ k)⁻¹ = z := by
    rw [← hact z hx.z_mem, hx.z_comm]
    group
  apply h.outer_not_mem_centralizer_V₀ hx
  rw [mem_centralizer_iff]
  intro w hw
  have hw' : x * w * x⁻¹ = w := by
    rw [hact w hw]
    by_cases hw1 : w = 1
    · rw [hw1]; group
    obtain ⟨j, hj⟩ := hb₀tr z hx.z_mem w hw hx.z_ne hw1
    rw [← hj]
    calc b₀ ^ k * ((b₀ ^ j)⁻¹ * z * b₀ ^ j) * (b₀ ^ k)⁻¹ =
        (b₀ ^ j)⁻¹ * (b₀ ^ k * z * (b₀ ^ k)⁻¹) * b₀ ^ j := by group
      _ = (b₀ ^ j)⁻¹ * z * b₀ ^ j := by rw [hz]
  calc w * x = x * w * x⁻¹ * x := by rw [hw']
    _ = x * w := by group

theorem outer_r_mem_X : r₁ ∈ rankTwoX A := by
  have hR2 : ∀ y ∈ R, y * y = 1 := fun y hy => h.mul_self (mem_sup_left hy)
  have hXn : (rankTwoX A).Normal := normalClosure_normal
  obtain ⟨r, hr, hr1, hrr₁⟩ := exists_ne_one_ne h.cardR hR2 hx.r_mem
  have hxr : x * r * x⁻¹ ∈ R := (mem_normalizer_iff.mp hx.normR r).mp hr
  have hxr1 : x * r * x⁻¹ ≠ 1 := fun h1 => hr1 (by
    calc r = x⁻¹ * (x * r * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group)
  have hxrr : x * r * x⁻¹ ≠ r := fun h1 => by
    rcases hx.fix_R r hr (by
      calc x * r = x * r * x⁻¹ * x := by group
        _ = r * x := by rw [h1]) with h2 | h2
    · exact hr1 h2
    · exact hrr₁ h2
  have hxrr₁ : x * r * x⁻¹ ≠ r₁ := fun h1 => hrr₁ (by
    calc r = x⁻¹ * (x * r * x⁻¹) * x := by group
      _ = x⁻¹ * (r₁ * x) := by rw [h1, mul_assoc]
      _ = x⁻¹ * (x * r₁) := by rw [hx.r_comm]
      _ = r₁ := by group)
  have hval : x * r * x⁻¹ = r * r₁ := by
    rcases mem_four h.cardR hR2 hr hx.r_mem hr1 hx.r_ne hrr₁ hxr with h1 | h1 | h1 | h1
    · exact absurd h1 hxr1
    · exact absurd h1 hxrr
    · exact absurd h1 hxrr₁
    · exact h1
  have hxG : x ∈ rankTwoX A ⊔ R := by rw [h.sup_top]; exact mem_top x
  obtain ⟨y, hy, s, hs, rfl⟩ := AS76b.exists_mul_of_mem_sup_of_le_normalizer
    (by rw [normalizer_eq_top_iff.mpr hXn]; exact le_top) hxG
  have hsr : s * r = r * s := h.comm (mem_sup_left hs) (mem_sup_left hr)
  have hmem : r⁻¹ * (y * s * r * (y * s)⁻¹) ∈ rankTwoX A := by
    have e : r⁻¹ * (y * s * r * (y * s)⁻¹) = (r⁻¹ * y * r) * y⁻¹ := by
      calc r⁻¹ * (y * s * r * (y * s)⁻¹) = r⁻¹ * y * (s * r) * s⁻¹ * y⁻¹ := by group
        _ = r⁻¹ * y * (r * s) * s⁻¹ * y⁻¹ := by rw [hsr]
        _ = (r⁻¹ * y * r) * y⁻¹ := by group
    rw [e]
    refine mul_mem ?_ (inv_mem hy)
    have := hXn.conj_mem y hy r⁻¹
    rwa [inv_inv] at this
  rw [hval] at hmem
  rwa [show r⁻¹ * (r * r₁) = r₁ by group] at hmem

end Setting310

theorem asc310IIb_of_steps (h4 : Asc310IIbStep4) (h56 : Asc310IIbStep56) : Asc310IIb := by
  intro G _ _ A R g T V₀ h hIIb
  obtain ⟨P, t, z₀, a, σ, c₁, hD⟩ := h4 G A R g T V₀ h hIIb
  refine ⟨h56 G A R g T V₀ P t z₀ a σ c₁ h hIIb hD, t, ?_, h.outer_mem_normalizer_A hD.outer,
    hD.outer.normR, h.outer_not_inner hD.outer⟩
  rw [sq]
  exact hD.outer.sq

end CFSG.ComponentClassification.RankTwoAltFive

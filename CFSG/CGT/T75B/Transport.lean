module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ T₂ : Subgroup G} {a : G}

theorem sec4N_conj_normalizer {w : G} (hw : w ∈ Subgroup.normalizer (T : Set G)) :
    sec4N T (conjSubgroup w T₁) (conjSubgroup w T₂) = conjSubgroup w (sec4N T T₁ T₂) := by
  have hT : conjSubgroup w T = T := mem_normalizer_iff_conjSubgroup_eq.1 hw
  have e1 := normIn_conj w T T₁
  have e2 := normIn_conj w T₁ T
  have e3 := normIn_conj w T₂ T
  rw [hT] at e1 e2 e3
  rw [sec4N, sec4N, e1, e2, e3, conjSubgroup_sup_eq_sup, conjSubgroup_sup_eq_sup]

theorem sec4Y_conj_normalizer {w : G} (hw : w ∈ Subgroup.normalizer (T : Set G)) :
    sec4Y T (conjSubgroup w T₁) (conjSubgroup w T₂) = conjSubgroup w (sec4Y T T₁ T₂) := by
  have hT : conjSubgroup w T = T := mem_normalizer_iff_conjSubgroup_eq.1 hw
  rw [sec4Y, sec4Y, conjSubgroup_sup_eq_sup, conjSubgroup_sup_eq_sup, hT]

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.conj_normalizer (h : Sec4Hyp T T₁ a T₂) {w : G}
    (hw : w ∈ Subgroup.normalizer (T : Set G)) :
    Sec4Hyp T (conjSubgroup w T₁) (w * a * w⁻¹) (conjSubgroup w T₂) := by
  have hT : conjSubgroup w T = T := mem_normalizer_iff_conjSubgroup_eq.1 hw
  have hwi : conjSubgroup w⁻¹ T = T :=
    mem_normalizer_iff_conjSubgroup_eq.1 ((Subgroup.normalizer (T : Set G)).inv_mem hw)
  have e1 := normIn_conj w T T₁
  rw [hT] at e1
  have hne : conjSubgroup w T₁ ≠ T := by
    intro h'
    apply h.pair.ne
    have : conjSubgroup w⁻¹ (conjSubgroup w T₁) = conjSubgroup w⁻¹ T := by rw [h']
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, hwi] at this
  have hne₂ : conjSubgroup w T₂ ≠ T := by
    intro h'
    apply h.ne_left
    have : conjSubgroup w⁻¹ (conjSubgroup w T₂) = conjSubgroup w⁻¹ T := by rw [h']
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, hwi] at this
  have hL : normIn T (conjSubgroup w T₁) = conjSubgroup w (normIn T T₁) := e1
  have hL₁ : normIn (conjSubgroup w T₁) T = conjSubgroup w (normIn T₁ T) := by
    have := normIn_conj w T₁ T
    rwa [hT] at this
  refine ⟨⟨h.pair.wc, ?_, hne, ?_, ?_⟩, h.glob, h.iso, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := h.pair.conj
    exact ⟨w * x, by rw [hx, conjSubgroup_conjSubgroup]⟩
  · rw [hL]
    exact fun hb => h.pair.nontriv (conjSubgroup_eq_bot_iff.1 hb)
  · intro g hg
    rw [hL, card_conjSubgroup]
    exact h.pair.maximal g hg
  ·
    obtain ⟨⟨k, t, ht, ht1, hak⟩, hanor⟩ := h.ha
    refine ⟨⟨k * w⁻¹, t, ht, ht1, ?_⟩, ?_⟩
    · have : (k * w⁻¹)⁻¹ * t * (k * w⁻¹) = w * (k⁻¹ * t * k) * w⁻¹ := by group
      rw [this, ← hak]
    · exact (Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hw hanor)
        ((Subgroup.normalizer (T : Set G)).inv_mem hw)
  ·
    intro hmem
    apply h.haL
    have h1 : w * a * w⁻¹ ∈ conjSubgroup w (T ⊔ normIn T₁ T) := by
      rw [conjSubgroup_sup_eq_sup, hT, ← hL₁]
      exact hmem
    rw [mem_conjSubgroup] at h1
    simpa [mul_assoc] using h1
  ·
    intro l hl
    rw [hL₁, mem_conjSubgroup] at hl
    have hcl := h.hcomm _ hl
    have e : (w⁻¹ * l * w) = w⁻¹ * l * w := rfl
    have key : ⁅w * a * w⁻¹, l⁆ = w * ⁅a, w⁻¹ * l * w⁆ * w⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    have := conj_mem_conjSubgroup w hcl
    rwa [hT] at this
  · obtain ⟨g, hg⟩ := h.conj
    exact ⟨w * g, by rw [hg, conjSubgroup_conjSubgroup]⟩
  · exact conj_mem_conjSubgroup w h.haT₂

section Finite

variable [Finite G]

theorem sec4N_conj_of_mem (h : Sec4Hyp T T₁ a T₂) {w : G} (hwY : w ∈ sec4Y T T₁ T₂)
    (hwT : w ∈ Subgroup.normalizer (T : Set G)) :
    sec4N T (conjSubgroup w T₁) (conjSubgroup w T₂) = sec4N T T₁ T₂ := by
  rw [sec4N_conj_normalizer hwT]
  exact mem_normalizer_iff_conjSubgroup_eq.1 (h.sec4Y_le_normalizer hwY)

omit [Finite G] in
theorem sec4Y_conj_of_mem {w : G} (hwY : w ∈ sec4Y T T₁ T₂)
    (hwT : w ∈ Subgroup.normalizer (T : Set G)) :
    sec4Y T (conjSubgroup w T₁) (conjSubgroup w T₂) = sec4Y T T₁ T₂ := by
  rw [sec4Y_conj_normalizer hwT]
  exact mem_normalizer_iff_conjSubgroup_eq.1 (Subgroup.le_normalizer hwY)

theorem sec4ActsTriv_conj_iff (h : Sec4Hyp T T₁ a T₂) {w : G} (hwY : w ∈ sec4Y T T₁ T₂)
    (hwT : w ∈ Subgroup.normalizer (T : Set G)) {x : G} :
    Sec4ActsTriv T (conjSubgroup w T₁) (conjSubgroup w T₂) x ↔ Sec4ActsTriv T T₁ T₂ x := by
  unfold Sec4ActsTriv
  rw [sec4Y_conj_of_mem hwY hwT, sec4N_conj_of_mem h hwY hwT]

end Finite

end CFSG.CGT.T75B

module

public import CFSG.CGT.Timmesfeld75.Sec3EightFixed
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB1

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.conj_of_mem_normalizer [Finite G] (h : Sec4Hyp T T₁ a T₂) {k : G}
    (hk : k ∈ Subgroup.normalizer (T : Set G)) :
    Sec4Hyp T (conjSubgroup k T₁) (k * a * k⁻¹) (conjSubgroup k T₂) := by
  have hkT : conjSubgroup k T = T := mem_normalizer_iff_conjSubgroup_eq.1 hk
  have hLk : normIn T (conjSubgroup k T₁) = conjSubgroup k (normIn T T₁) :=
    normIn_conj_left_of_mem_normalizer hk T₁
  have hL₁k : normIn (conjSubgroup k T₁) T = conjSubgroup k (normIn T₁ T) :=
    normIn_conj_right_of_mem_normalizer hk T₁
  obtain ⟨x, hx⟩ := h.pair.conj
  obtain ⟨y, hy⟩ := h.conj
  refine ⟨⟨h.pair.wc, ⟨k * x, ?_⟩, ?_, ?_, ?_⟩, h.glob, h.iso, ?_, ?_, ?_, ⟨k * y, ?_⟩, ?_⟩
  · rw [hx, conjSubgroup_conjSubgroup]
  · intro h1
    apply h.pair.ne
    have h2 := congrArg (conjSubgroup k⁻¹) h1
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
      mem_normalizer_iff_conjSubgroup_eq.1 ((Subgroup.normalizer _).inv_mem hk)] at h2
  · rw [hLk]
    intro h1
    exact h.pair.nontriv (conjSubgroup_eq_bot_iff.1 h1)
  · intro g hg
    rw [hLk, card_conjSubgroup]
    exact h.pair.maximal g hg
  · obtain ⟨k₀, t, ht, ht1, hak⟩ := h.ha.1
    refine ⟨⟨k₀ * k⁻¹, t, ht, ht1, ?_⟩, ?_⟩
    · rw [hak]
      group
    · exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hk h.ha.2)
        ((Subgroup.normalizer _).inv_mem hk)
  · rw [hL₁k]
    have e2 : T ⊔ conjSubgroup k (normIn T₁ T) = conjSubgroup k (T ⊔ normIn T₁ T) := by
      rw [conjSubgroup_sup_eq_sup, hkT]
    rw [e2]
    intro hmem
    apply h.haL
    rw [mem_conjSubgroup] at hmem
    have e : k⁻¹ * (k * a * k⁻¹) * k = a := by group
    rwa [e] at hmem
  · intro l hl
    rw [hL₁k] at hl
    obtain ⟨l₀, hl₀, rfl⟩ := mem_conjSubgroup_iff_exists.1 hl
    have e : ⁅k * a * k⁻¹, k * l₀ * k⁻¹⁆ = k * ⁅a, l₀⁆ * k⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_of_mem_normalizer hk (h.hcomm l₀ hl₀)
  · rw [hy, conjSubgroup_conjSubgroup]
  · exact conj_mem_conjSubgroup k h.haT₂

end CFSG.CGT.Timmesfeld75

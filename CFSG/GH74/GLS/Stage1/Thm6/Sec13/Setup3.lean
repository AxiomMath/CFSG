module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fixed
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Comm
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Setup1

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Out12

variable {x : G} {T V : Subgroup G} (h : Out12 G x T V)
include h

theorem exists_f0 [Finite G] : ∃ f : G, Is3Element f ∧ f ∈ centralizer ({x} : Set G) ∧
    f ∈ normalizer (EV x V : Set G) ∧ f ∈ normalizer (V : Set G) ∧
    f ∉ centralizer (V : Set G) ∧ (∀ v ∈ V, f * v * f⁻¹ = v → v = 1) ∧
    EV x V ⊓ centralizer ({f} : Set G) = zpowers x := by
  obtain ⟨f, hf3, hfx, hfE, hcomm⟩ := h.f_x
  have hfV : f ∈ normalizer (V : Set G) := by
    have := mem_normalizer_commutator hfE
    rwa [hcomm] at this
  have hfnc : f ∉ centralizer (V : Set G) := by
    intro hc
    have hcE : f ∈ centralizer (EV x V : Set G) := by
      rw [mem_centralizer_iff]
      intro e he
      have hxf : x * f = f * x := mem_centralizer_iff.1 hfx x rfl
      have hvf : ∀ v ∈ V, v * f = f * v := fun v hv => mem_centralizer_iff.1 hc v hv
      obtain ⟨v, hv, he' | he'⟩ := (h.mem_EV).1 he <;> rw [he']
      · exact hvf v hv
      · calc v * x * f = v * (x * f) := by group
          _ = v * (f * x) := by rw [hxf]
          _ = (v * f) * x := by group
          _ = (f * v) * x := by rw [hvf v hv]
          _ = f * (v * x) := by group
    have hbot : ⁅zpowers f, EV x V⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer, zpowers_le]
      exact hcE
    rw [hcomm] at hbot
    have : Nat.card V = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h4 : Nat.card V = 4 := h.V_four.2
    omega
  obtain ⟨k, hk⟩ := hf3
  have hN : ∀ v ∈ V, f * v * f⁻¹ ∈ V := fun v hv => (mem_normalizer_iff.1 hfV v).1 hv
  have hnc : ∃ v ∈ V, f * v * f⁻¹ ≠ v := by
    by_contra hcon
    push Not at hcon
    apply hfnc
    rw [mem_centralizer_iff]
    intro v hv
    have := hcon v hv
    calc v * f = (f * v * f⁻¹) * f := by rw [this]
      _ = f * v := by group
  have hfix := fix_free_four V f k hk hN h.V_four.2 hnc
  refine ⟨f, ⟨k, hk⟩, hfx, hfE, hfV, hfnc, hfix, ?_⟩
  ext g
  constructor
  · rintro ⟨hgE, hgf⟩
    have hfg : f * g = g * f := (mem_centralizer_iff.1 hgf f rfl)
    have hfx' : f * x * f⁻¹ = x := by
      have := mem_centralizer_iff.1 hfx x rfl
      calc f * x * f⁻¹ = (x * f) * f⁻¹ := by rw [this]
        _ = x := by group
    obtain ⟨v, hv, hg | hg⟩ := (h.mem_EV).1 hgE
    · have : v = 1 := by
        apply hfix v hv
        rw [hg] at hfg
        calc f * v * f⁻¹ = (v * f) * f⁻¹ := by rw [hfg]
          _ = v := by group
      rw [hg, this]; exact one_mem _
    · have hv1 : f * v * f⁻¹ = v := by
        rw [hg] at hfg
        have : (f * v * f⁻¹) * x = v * x := by
          calc (f * v * f⁻¹) * x = (f * v * f⁻¹) * (f * x * f⁻¹) := by rw [hfx']
            _ = f * (v * x) * f⁻¹ := by group
            _ = (v * x * f) * f⁻¹ := by rw [hfg]
            _ = v * x := by group
        exact mul_right_cancel this
      have : v = 1 := hfix v hv hv1
      rw [hg, this, one_mul]; exact mem_zpowers x
  · intro hg
    rw [mem_zpowers_involution h.x_sq] at hg
    rcases hg with hg | hg
    · rw [hg]; exact ⟨one_mem _, one_mem _⟩
    · rw [hg]
      refine ⟨x_mem_EV, ?_⟩
      show x ∈ centralizer ({f} : Set G)
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (mem_centralizer_iff.1 hfx x rfl).symm

end Out12

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

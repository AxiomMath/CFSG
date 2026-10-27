module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6QP
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S5F

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

section C7


namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem P_comm_sq_mem_V₃ (h : d.Hyp) (hKl : d.KLinear) :
    (∀ x ∈ d.P, ∀ y ∈ d.P, x * y * x⁻¹ * y⁻¹ ∈ d.V₃) ∧ ∀ x ∈ d.P, x * x ∈ d.V₃ := by
  have hK := h.comm_M_V₂_mem_W_linear hKl
  have hKY := h.M_le_normalizer_Y_linear hKl
  have hD := h.D₁_le_normalizer_D₂ hK hKY
  obtain ⟨U₁, U₂, hU₁, hU₂, hMY, hU₁c, hU₁s, hU₂c, hU₂s, hU₁₂, hI₁, hI₂, hII⟩ :=
    h.exists_quad_pkg hKl hD
  have hMYN : d.M ⊔ d.Y ≤ normalizer (d.V₃ : Set G) :=
    sup_le (M_le_D₁.trans (h.D₁_le_normalizer_V₃ hKY)) (h.Y_le_D₂.trans h.D₂_le_normalizer_V₃)
  have hD₂N : d.D₂ ≤ normalizer (d.V₃ : Set G) := h.D₂_le_normalizer_V₃
  have hU₁N : U₁ ≤ normalizer (d.V₃ : Set G) := hU₁.trans hMYN
  have hU₂N : U₂ ≤ normalizer (d.V₃ : Set G) := hU₂.trans hMYN
  have hA₁N : d.D₂ ⊔ U₁ ≤ normalizer (d.V₃ : Set G) := sup_le hD₂N hU₁N
  have hYV : d.Y ≤ d.V₃ := h.Y_le_V₃
  have hPQ : d.P ≤ d.D₂ ⊔ U₁ ⊔ U₂ := by
    refine sup_le ?_ (le_sup_left.trans le_sup_left)
    rw [h.D₁_eq_D₃e₂_sup_M]
    refine sup_le ((h.D₃e₂_le_D₂).trans (le_sup_left.trans le_sup_left)) ?_
    exact le_sup_left.trans (hMY.trans (sup_le (sup_le (le_sup_right.trans le_sup_left)
      le_sup_right) (h.Y_le_D₂.trans (le_sup_left.trans le_sup_left))))
  have hcomm_one : ∀ {A : Subgroup G}, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ∀ b ∈ A, ∀ b' ∈ A, ⁅b, b'⁆ ∈ d.V₃ := fun hA b hb b' hb' => by
    have : ⁅b, b'⁆ = 1 := by rw [commutatorElement_def, hA b hb b' hb']; group
    rw [this]
    exact one_mem _
  have hinvI₁ : ∀ a ∈ d.D₂, ∀ b ∈ U₁, ⁅a, b⁆ ∈ d.V₃ := fun a ha b hb => by
    rw [← commutatorElement_inv]
    exact d.V₃.inv_mem (hI₁ b hb a ha)
  have hinvI₂ : ∀ a ∈ d.D₂, ∀ b ∈ U₂, ⁅a, b⁆ ∈ d.V₃ := fun a ha b hb => by
    rw [← commutatorElement_inv]
    exact d.V₃.inv_mem (hI₂ b hb a ha)
  have h1 : ⁅d.D₂ ⊔ U₁, d.D₂ ⊔ U₁⁆ ≤ d.V₃ := by
    refine commutator_sup_le_of hD₂N hU₁N ?_ (hcomm_one hU₁c) hinvI₁
    intro a ha a' ha'
    exact hYV (h.D₂_commutator_mem_Y hK ha ha')
  have h2 : ⁅d.D₂ ⊔ U₁ ⊔ U₂, d.D₂ ⊔ U₁ ⊔ U₂⁆ ≤ d.V₃ := by
    refine commutator_sup_le_of hA₁N hU₂N ?_ (hcomm_one hU₂c) ?_
    · intro a ha a' ha'
      exact h1 (Subgroup.commutator_mem_commutator ha ha')
    · intro a ha b hb
      have hle : d.D₂ ⊔ U₁ ≤ centModSub d.V₃ b := by
        refine sup_le (fun x hx => mem_centModSub.2 ⟨hD₂N hx, ?_⟩)
          (fun x hx => mem_centModSub.2 ⟨hU₁N hx, ?_⟩)
        · have := hinvI₂ x hx b hb
          rwa [commutatorElement_def] at this
        · have : x * b * x⁻¹ * b⁻¹ = 1 := by rw [hU₁₂ x hx b hb]; group
          rw [this]
          exact one_mem _
      exact (mem_centModSub.1 (hle ha)).2
  have hcomm : ∀ x ∈ d.P, ∀ y ∈ d.P, x * y * x⁻¹ * y⁻¹ ∈ d.V₃ := fun x hx y hy =>
    h2 (Subgroup.commutator_mem_commutator (hPQ hx) (hPQ hy))
  refine ⟨hcomm, ?_⟩
  let Sq : Subgroup G :=
    { carrier := {x | x ∈ d.D₂ ⊔ U₁ ⊔ U₂ ∧ x * x ∈ d.V₃}
      one_mem' := ⟨one_mem _, by simpa using d.V₃.one_mem⟩
      mul_mem' := by
        rintro x y ⟨hxQ, hx2⟩ ⟨hyQ, hy2⟩
        refine ⟨mul_mem hxQ hyQ, ?_⟩
        have hc : x * y * x⁻¹ * y⁻¹ ∈ d.V₃ := h2 (Subgroup.commutator_mem_commutator hxQ hyQ)
        have hyN : y ∈ normalizer (d.V₃ : Set G) := (sup_le hA₁N hU₂N) hyQ
        have e : x * y * (x * y) = (x * y * x⁻¹ * y⁻¹) * (y * (x * x) * y⁻¹) * (y * y) := by
          group
        rw [e]
        exact mul_mem (mul_mem hc ((mem_normalizer_iff.1 hyN _).1 hx2)) hy2
      inv_mem' := by
        rintro x ⟨hxQ, hx2⟩
        refine ⟨inv_mem hxQ, ?_⟩
        have e : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        rw [e]
        exact inv_mem hx2 }
  have hQSq : d.D₂ ⊔ U₁ ⊔ U₂ ≤ Sq := by
    refine sup_le (sup_le (fun x hx => ⟨mem_sup_left (mem_sup_left hx), ?_⟩)
      (fun x hx => ⟨mem_sup_left (mem_sup_right hx), ?_⟩))
      (fun x hx => ⟨mem_sup_right hx, ?_⟩)
    · exact hYV (h.D₂_mul_self_mem_Y hK hx)
    · rw [hU₁s x hx]
      exact one_mem _
    · rw [hU₂s x hx]
      exact one_mem _
  exact fun x hx => (hQSq (hPQ hx)).2

theorem S₃_le_commutator_T (h : d.Hyp) (hKl : d.KLinear) :
    d.S₃ ≤ ⁅d.P ⊔ zpowers d.t, d.P ⊔ zpowers d.t⁆ := by
  have hK := h.comm_M_V₂_mem_W_linear hKl
  have hKY := h.M_le_normalizer_Y_linear hKl
  have hD := h.D₁_le_normalizer_D₂ hK hKY
  obtain ⟨U₁, U₂, hU₁, hU₂, -, -, -, -, -, -, -, -, hII⟩ := h.exists_quad_pkg hKl hD
  have hPT : d.P ≤ d.P ⊔ zpowers d.t := le_sup_left
  have htT : d.t ∈ d.P ⊔ zpowers d.t := mem_sup_right (mem_zpowers _)
  have hMYP : d.M ⊔ d.Y ≤ d.P :=
    sup_le (M_le_D₁.trans D₁_le_P) (h.Y_le_D₂.trans D₂_le_P)
  have hD₂T : d.D₂ ≤ d.P ⊔ zpowers d.t := D₂_le_P.trans hPT
  have hV₃ : d.V₃ ≤ ⁅d.P ⊔ zpowers d.t, d.P ⊔ zpowers d.t⁆ := by
    intro c hc
    obtain ⟨u₁, hu₁, u₂, hu₂, x₁, hx₁, x₂, hx₂, y, hy, rfl⟩ := hII c hc
    have hY : y ∈ ⁅d.P ⊔ zpowers d.t, d.P ⊔ zpowers d.t⁆ := by
      have := h.commutator_D₂_eq_Y hK
      rw [← this] at hy
      exact Subgroup.commutator_mono hD₂T hD₂T hy
    refine mul_mem (mul_mem ?_ ?_) hY
    · exact Subgroup.commutator_mem_commutator (hPT (hMYP (hU₁ hu₁))) (hD₂T hx₁)
    · exact Subgroup.commutator_mem_commutator (hPT (hMYP (hU₂ hu₂))) (hD₂T hx₂)
  intro g hg
  obtain ⟨p, hp, hpg⟩ := h.exists_mem_P₀_theta_mul_mem_V₃ hK hKY hg
  have hpP : p ∈ d.P := by
    rw [h.P_eq_P₀ hK hKY]
    exact hp
  have hθ : p * d.t * p⁻¹ * d.t ∈ ⁅d.P ⊔ zpowers d.t, d.P ⊔ zpowers d.t⁆ := by
    have := Subgroup.commutator_mem_commutator (hPT hpP) htT
    rwa [commutatorElement_def, h.t_inv] at this
  have e : g = (p * d.t * p⁻¹ * d.t) * ((p * d.t * p⁻¹ * d.t)⁻¹ * g) := by group
  rw [e]
  exact mul_mem hθ (hV₃ hpg)

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

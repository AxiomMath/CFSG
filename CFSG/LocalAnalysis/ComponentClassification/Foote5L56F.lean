module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56C

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_involution_swap {X X' : Subgroup G} (hcomm : ∀ c ∈ X, ∀ d ∈ X', c * d = d * c)
    (hbot : X ⊓ X' = ⊥) {s : G} (hsX : ∀ c ∈ X, s⁻¹ * c * s ∈ X')
    (hsX' : ∀ c ∈ X', s⁻¹ * c * s ∈ X) (hs2 : s * s ∈ X ⊔ X') :
    ∃ c₁ ∈ X, (c₁⁻¹ * s) * (c₁⁻¹ * s) = 1 ∧
      (∀ c ∈ X, (c₁⁻¹ * s) * c * (c₁⁻¹ * s) ∈ X') ∧
      ∀ c ∈ X', (c₁⁻¹ * s) * c * (c₁⁻¹ * s) ∈ X := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hs⟩ := exists_mul_of_mem_sup_commute hcomm hs2
  have h1 : s⁻¹ * c₂ * s * (s⁻¹ * c₁ * s) = c₁ * c₂ := by
    calc s⁻¹ * c₂ * s * (s⁻¹ * c₁ * s) = s⁻¹ * c₁ * s * (s⁻¹ * c₂ * s) :=
          hcomm _ (hsX' c₂ hc₂) _ (hsX c₁ hc₁)
      _ = s⁻¹ * (c₁ * c₂) * s := by group
      _ = c₁ * c₂ := by rw [← hs]; group
  obtain ⟨e₁, -⟩ := eq_of_mul_eq_mul_of_disjoint hbot (hsX' c₂ hc₂) hc₁ (hsX c₁ hc₁) hc₂ h1
  have e₂ : s * c₁ * s⁻¹ = c₂ := by rw [← e₁]; group
  have hinv : (c₁⁻¹ * s) * (c₁⁻¹ * s) = 1 := by
    calc (c₁⁻¹ * s) * (c₁⁻¹ * s) = c₁⁻¹ * (s * c₁ * s⁻¹)⁻¹ * (s * s) := by group
      _ = c₁⁻¹ * c₂⁻¹ * (c₁ * c₂) := by rw [e₂, hs]
      _ = c₁⁻¹ * c₂⁻¹ * (c₂ * c₁) := by rw [hcomm c₁ hc₁ c₂ hc₂]
      _ = 1 := by group
  have hs₀ : c₁⁻¹ * s = (c₁⁻¹ * s)⁻¹ := (inv_eq_of_mul_eq_one_right hinv).symm
  refine ⟨c₁, hc₁, hinv, fun c hc => ?_, fun c hc => ?_⟩
  · rw [show (c₁⁻¹ * s) * c * (c₁⁻¹ * s) = (c₁⁻¹ * s)⁻¹ * c * (c₁⁻¹ * s) by
      rw [← hs₀]]
    rw [show (c₁⁻¹ * s)⁻¹ * c * (c₁⁻¹ * s) = s⁻¹ * (c₁ * c * c₁⁻¹) * s by group]
    exact hsX _ (mul_mem (mul_mem hc₁ hc) (inv_mem hc₁))
  · rw [show (c₁⁻¹ * s) * c * (c₁⁻¹ * s) = (c₁⁻¹ * s)⁻¹ * c * (c₁⁻¹ * s) by
      rw [← hs₀]]
    rw [show (c₁⁻¹ * s)⁻¹ * c * (c₁⁻¹ * s) = s⁻¹ * (c₁ * c * c₁⁻¹) * s by group,
      show c₁ * c * c₁⁻¹ = c by rw [hcomm c₁ hc₁ c hc, mul_inv_cancel_right]]
    exact hsX' c hc

namespace WreathCfg

variable {T X X' : Subgroup G} {x a s : G} (h : WreathCfg T X X' x a s)
include h

theorem s_comm_mul_conj {c : G} (hc : c ∈ X) :
    s * (c * (s * c * s)) = c * (s * c * s) * s := by
  have h1 : c * (s * c * s) = s * c * s * c := h.comm c hc _ (h.sX c hc)
  calc s * (c * (s * c * s)) = s * (s * c * s * c) := by rw [h1]
    _ = (s * s) * c * s * c := by group
    _ = c * s * c := by rw [h.s2, one_mul]
    _ = c * (s * c * s) * s := by
        rw [show c * (s * c * s) * s = c * s * c * (s * s) by group, h.s2, mul_one]

theorem diag_sq {c : G} (hc : c ∈ X) (hcc : c * c = 1) :
    c * (s * c * s) * (c * (s * c * s)) = 1 := by
  have h1 := h.comm c hc _ (h.sX c hc)
  calc c * (s * c * s) * (c * (s * c * s)) = c * (s * c * s * c) * (s * c * s) := by group
    _ = c * (c * (s * c * s)) * (s * c * s) := by rw [h1]
    _ = (c * c) * (s * c * (s * s) * c * s) := by group
    _ = (c * c) * (s * (c * c) * s) := by rw [h.s2, mul_one]; group
    _ = 1 := by rw [hcc, mul_one, one_mul, h.s2]

theorem diag_comm {c d : G} (hc : c ∈ X) (hd : d ∈ X) (hcd : c * d = d * c) :
    c * (s * c * s) * (d * (s * d * s)) = d * (s * d * s) * (c * (s * c * s)) := by
  have h1 : (s * c * s) * (s * d * s) = (s * d * s) * (s * c * s) := by
    calc (s * c * s) * (s * d * s) = s * c * (s * s) * d * s := by group
      _ = s * (c * d) * s := by rw [h.s2]; group
      _ = s * (d * c) * s := by rw [hcd]
      _ = s * d * (s * s) * c * s := by rw [h.s2]; group
      _ = (s * d * s) * (s * c * s) := by group
  have h2 := h.comm d hd _ (h.sX c hc)
  have h3 := h.comm c hc _ (h.sX d hd)
  calc c * (s * c * s) * (d * (s * d * s)) = c * ((s * c * s) * d) * (s * d * s) := by group
    _ = c * (d * (s * c * s)) * (s * d * s) := by rw [h2]
    _ = (c * d) * ((s * c * s) * (s * d * s)) := by group
    _ = (d * c) * ((s * d * s) * (s * c * s)) := by rw [hcd, h1]
    _ = d * (c * (s * d * s)) * (s * c * s) := by group
    _ = d * ((s * d * s) * c) * (s * c * s) := by rw [h3]
    _ = d * (s * d * s) * (c * (s * c * s)) := by group

theorem eq_of_commute_s_diag [Finite G] {w : G} (hw : w ∈ X ⊔ X') (hws : w * s = s * w)
    (hwr : w * (a * (s * a * s)) = a * (s * a * s) * w) :
    w = x * (s * x * s) * (a * (s * a * s)) ∨ w = x * (s * x * s) ∨
      w = a * (s * a * s) ∨ w = 1 := by
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := exists_mul_of_mem_sup_commute h.comm hw
  have h1 : s * q₂ * s * (s * q₁ * s) = q₁ * q₂ := by
    calc s * q₂ * s * (s * q₁ * s) = s * q₁ * s * (s * q₂ * s) :=
          h.comm _ (h.sX' q₂ hq₂) _ (h.sX q₁ hq₁)
      _ = s * q₁ * (s * s) * q₂ * s := by group
      _ = s * (q₁ * q₂) * s := by rw [h.s2]; group
      _ = q₁ * q₂ := by rw [← hws, mul_assoc (q₁ * q₂), h.s2, mul_one]
  obtain ⟨-, e₂⟩ := eq_of_mul_eq_mul_of_disjoint h.bot (h.sX' q₂ hq₂) hq₁ (h.sX q₁ hq₁) hq₂ h1
  have ha'X' := h.sX a h.aX
  have h2 : q₁ * a * (q₂ * (s * a * s)) = a * q₁ * ((s * a * s) * q₂) := by
    calc q₁ * a * (q₂ * (s * a * s)) = q₁ * (a * q₂) * (s * a * s) := by group
      _ = q₁ * (q₂ * a) * (s * a * s) := by rw [h.comm a h.aX q₂ hq₂]
      _ = q₁ * q₂ * (a * (s * a * s)) := by group
      _ = a * (s * a * s) * (q₁ * q₂) := hwr
      _ = a * ((s * a * s) * q₁) * q₂ := by group
      _ = a * (q₁ * (s * a * s)) * q₂ := by rw [h.comm q₁ hq₁ _ ha'X']
      _ = a * q₁ * ((s * a * s) * q₂) := by group
  obtain ⟨e₃, -⟩ := eq_of_mul_eq_mul_of_disjoint h.bot (mul_mem hq₁ h.aX) (mul_mem h.aX hq₁)
    (mul_mem hq₂ ha'X') (mul_mem ha'X' hq₂) h2
  rw [← e₂]
  have hxa : x * a = a * x := (h.xZ a h.aX).symm
  rcases mem_four_of_commute_noncentral h.card h.xX h.x2 h.x1 h.xZ h.aX h.a2 h.anc hq₁ e₃
    with e | e | e | e <;> rw [e]
  · left
    have hx'X' := h.sX x h.xX
    have hx'a' : (s * x * s) * (s * a * s) = (s * a * s) * (s * x * s) := by
      calc (s * x * s) * (s * a * s) = s * x * (s * s) * a * s := by group
        _ = s * (x * a) * s := by rw [h.s2]; group
        _ = s * (a * x) * s := by rw [hxa]
        _ = s * a * (s * s) * x * s := by rw [h.s2]; group
        _ = (s * a * s) * (s * x * s) := by group
    calc a * x * (s * (a * x) * s) = a * x * ((s * a * s) * (s * x * s)) := by
          rw [show s * (a * x) * s = s * a * (s * s) * x * s by rw [h.s2]; group]; group
      _ = x * a * ((s * x * s) * (s * a * s)) := by rw [hxa, hx'a']
      _ = x * (a * (s * x * s)) * (s * a * s) := by group
      _ = x * ((s * x * s) * a) * (s * a * s) := by rw [h.comm a h.aX _ hx'X']
      _ = x * (s * x * s) * (a * (s * a * s)) := by group
  · right; right; left; rfl
  · right; left; rfl
  · right; right; right
    rw [one_mul, mul_one, h.s2]

end WreathCfg

end CFSG.ComponentClassification.Foote5

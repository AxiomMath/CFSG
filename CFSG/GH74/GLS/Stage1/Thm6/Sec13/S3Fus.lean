module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fin4
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Setup2

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem Out12.abelian_card_lt_16 [Finite G] {x : G} {T V : Subgroup G} (hout : Out12 G x T V)
    {A : Subgroup G} (hAC : A ≤ centralizer ({x} : Set G)) (hA2 : IsPGroup 2 ↥A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nat.card A < 16 := by
  by_contra hge
  push Not at hge
  obtain ⟨T', hT', hAT'⟩ := SylowIn.exists_ge (p := 2) hAC hA2
  have hT : Sylow2In T (centralizer ({x} : Set G)) := hout.T_sylow
  have hcard := card_eq_of_sylow hT hT'
  have hAle := Subgroup.card_le_of_le hAT'
  have hT16 : Nat.card T = 16 := by
    have := hout.T_card
    omega
  have hAT : A = T' := by
    apply Subgroup.eq_of_le_of_card_ge hAT'
    rw [hcard, hT16]
    omega
  obtain ⟨c, -, hc⟩ := SylowIn.conj (p := 2) (P := T) (Q := T') (C := centralizer ({x} : Set G)) hT hT'
  have hTab : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ * t₂ = t₂ * t₁ := by
    intro t₁ ht₁ t₂ ht₂
    have e1 : c⁻¹ * (c * t₁ * c⁻¹) * c = t₁ := by group
    have e2 : c⁻¹ * (c * t₂ * c⁻¹) * c = t₂ := by group
    have h1 : c * t₁ * c⁻¹ ∈ T' := (hc _).2 (by rw [e1]; exact ht₁)
    have h2 : c * t₂ * c⁻¹ ∈ T' := (hc _).2 (by rw [e2]; exact ht₂)
    rw [← hAT] at h1 h2
    have h3 := hAab _ h1 _ h2
    have e : c⁻¹ * ((c * t₁ * c⁻¹) * (c * t₂ * c⁻¹)) * c = t₁ * t₂ := by group
    have e' : c⁻¹ * ((c * t₂ * c⁻¹) * (c * t₁ * c⁻¹)) * c = t₂ * t₁ := by group
    calc t₁ * t₂ = c⁻¹ * ((c * t₁ * c⁻¹) * (c * t₂ * c⁻¹)) * c := e.symm
      _ = c⁻¹ * ((c * t₂ * c⁻¹) * (c * t₁ * c⁻¹)) * c := by rw [h3]
      _ = t₂ * t₁ := e'
  have hTC : T ≤ centralizer (EV x V : Set G) := by
    intro t ht
    rw [mem_centralizer_iff]
    intro e he
    exact hTab e (hout.E_le_T he) t ht
  have hTE : T ≤ EV x V := by
    intro t ht
    rw [← hout.E_cent]
    exact ⟨ht, hTC ht⟩
  have := Subgroup.card_le_of_le hTE
  rw [hout.card_EV, hT16] at this
  omega

theorem not_fused_of_abelian [Finite G] {x : G} {T V P : Subgroup G} (hout : Out12 G x T V)
    (hP2 : IsPGroup 2 ↥P)
    (hA : ∀ u ∈ P, u * u = 1 → ∃ A : Subgroup G, A ≤ P ∧ u ∈ A ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ 16 ≤ Nat.card A) (g : G) : g * x * g⁻¹ ∉ P := by
  intro hu
  have hu2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hout.x_sq]; group
  obtain ⟨A, hAP, huA, hAab, hA16⟩ := hA _ hu hu2
  have hAmem : ∀ a : G, a ∈ cj g⁻¹ A ↔ g * a * g⁻¹ ∈ A := by
    intro a
    rw [mem_cj]
    simp
  have hAC : cj g⁻¹ A ≤ centralizer ({x} : Set G) := by
    intro a ha
    have ha' : g * a * g⁻¹ ∈ A := (hAmem a).1 ha
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have h1 := hAab _ huA _ ha'
    have e : g * (x * a) * g⁻¹ = g * (a * x) * g⁻¹ := by
      calc g * (x * a) * g⁻¹ = (g * x * g⁻¹) * (g * a * g⁻¹) := by group
        _ = (g * a * g⁻¹) * (g * x * g⁻¹) := h1
        _ = g * (a * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have hAab' : ∀ a ∈ cj g⁻¹ A, ∀ b ∈ cj g⁻¹ A, a * b = b * a := by
    intro a ha b hb
    have ha' := (hAmem a).1 ha
    have hb' := (hAmem b).1 hb
    have h1 := hAab _ ha' _ hb'
    have e : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h1
        _ = g * (b * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have hA2 : IsPGroup 2 ↥(cj g⁻¹ A) := (hP2.to_le hAP).map _
  have hlt := hout.abelian_card_lt_16 hAC hA2 hAab'
  rw [card_cj] at hlt
  omega

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

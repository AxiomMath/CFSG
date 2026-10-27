module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fin4
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fin2
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Setup2

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem T_eq_inf [Finite G] {x : G} {T V S : Subgroup G} (hout : Out12 G x T V)
    (hS2 : IsPGroup 2 ↥S) (hTS : T ≤ S) : S ⊓ centralizer ({x} : Set G) = T :=
  eq_of_sylow_le hout.T_sylow inf_le_right (le_inf hTS hout.T_sylow.1) (hS2.to_le inf_le_left)

theorem card_T_eq_16 [Finite G] {x : G} {T V H : Subgroup G} (hout : Out12 G x T V)
    (hTH : T ⊓ H = EV x V) (hnle : ¬ T ≤ H) : Nat.card T = 16 := by
  have h8 : 8 ∣ Nat.card T := by
    have := Subgroup.card_dvd_of_le (inf_le_left : T ⊓ H ≤ T)
    rwa [hTH, hout.card_EV] at this
  have hlt : T ⊓ H < T := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    exact hnle (h ▸ inf_le_right)
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [hTH, hout.card_EV] at h1
  have h2 := hout.T_card
  omega

theorem not_fused [Finite G] {x : G} {T V H₀ : Subgroup G} {a b : G} (hout : Out12 G x T V)
    (hT16 : Nat.card T = 16) (z4 : Z4Data H₀ a b) (g : G) : g * x * g⁻¹ ∉ H₀ := by
  intro hy
  have hAmem : ∀ u : G, u ∈ cj g⁻¹ H₀ ↔ g * u * g⁻¹ ∈ H₀ := by
    intro u
    rw [mem_cj]
    simp
  have hA16 : Nat.card ↥(cj g⁻¹ H₀) = 16 := by rw [card_cj, z4.card]
  have hAC : cj g⁻¹ H₀ ≤ centralizer ({x} : Set G) := by
    intro u hu
    have hu' : g * u * g⁻¹ ∈ H₀ := (hAmem u).1 hu
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have h1 := z4.comm hu' hy
    have e : g * (x * u) * g⁻¹ = g * (u * x) * g⁻¹ := by
      calc g * (x * u) * g⁻¹ = (g * x * g⁻¹) * (g * u * g⁻¹) := by group
        _ = (g * u * g⁻¹) * (g * x * g⁻¹) := h1.symm
        _ = g * (u * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have hAp : IsPGroup 2 ↥(cj g⁻¹ H₀) := IsPGroup.of_card (n := 4) (by rw [hA16]; norm_num)
  obtain ⟨T', hT', hAT'⟩ := SylowIn.exists_ge (p := 2) hAC hAp
  have hT : Sylow2In T (centralizer ({x} : Set G)) := hout.T_sylow
  have hcard := card_eq_of_sylow hT hT'
  have hAT : cj g⁻¹ H₀ = T' := by
    apply Subgroup.eq_of_le_of_card_ge hAT'
    rw [hcard, hT16, hA16]
  obtain ⟨c, -, hc⟩ := SylowIn.conj (p := 2) (P := T) (Q := T') (C := centralizer ({x} : Set G)) hT hT'
  have hTab : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ * t₂ = t₂ * t₁ := by
    intro t₁ ht₁ t₂ ht₂
    have e1 : c⁻¹ * (c * t₁ * c⁻¹) * c = t₁ := by group
    have e2 : c⁻¹ * (c * t₂ * c⁻¹) * c = t₂ := by group
    have h1 : c * t₁ * c⁻¹ ∈ T' := (hc _).2 (by rw [e1]; exact ht₁)
    have h2 : c * t₂ * c⁻¹ ∈ T' := (hc _).2 (by rw [e2]; exact ht₂)
    rw [← hAT, hAmem] at h1 h2
    have h3 := z4.comm h1 h2
    have e : c⁻¹ * g⁻¹ * ((g * (c * t₁ * c⁻¹) * g⁻¹) * (g * (c * t₂ * c⁻¹) * g⁻¹)) * g * c =
        t₁ * t₂ := by group
    have e' : c⁻¹ * g⁻¹ * ((g * (c * t₂ * c⁻¹) * g⁻¹) * (g * (c * t₁ * c⁻¹) * g⁻¹)) * g * c =
        t₂ * t₁ := by group
    calc t₁ * t₂ = c⁻¹ * g⁻¹ * ((g * (c * t₁ * c⁻¹) * g⁻¹) * (g * (c * t₂ * c⁻¹) * g⁻¹)) * g * c :=
          e.symm
      _ = c⁻¹ * g⁻¹ * ((g * (c * t₂ * c⁻¹) * g⁻¹) * (g * (c * t₁ * c⁻¹) * g⁻¹)) * g * c := by
          rw [h3]
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

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

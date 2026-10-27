module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Setup1
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.SylowB

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Out12

variable {x : G} {T V : Subgroup G} (h : Out12 G x T V)
include h

theorem card_EV : Nat.card (EV x V) = 8 := by
  have hV4 : Nat.card V = 4 := h.V_four.2
  have hrel : V.relIndex (EV x V) = 2 := by
    have hdvd : V.relIndex (EV x V) ∣ 2 := by
      rw [relIndex_dvd_two_iff]
      refine ⟨x, x_mem_EV, ?_⟩
      intro b hb
      obtain ⟨v, hv, hb' | hb'⟩ := (h.mem_EV).1 hb
      · right; rw [hb']; exact hv
      · left
        have : v * x * x = v := by rw [mul_assoc, h.x_sq, mul_one]
        rw [hb', this]; exact hv
    have hne : V.relIndex (EV x V) ≠ 1 := by
      intro h1
      rw [relIndex_eq_one] at h1
      exact h.x_not_mem (h1 x_mem_EV)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have := relIndex_mul_card V (EV x V)
  rw [inf_of_le_left V_le_EV, hrel, hV4] at this
  omega

theorem E_le_C : EV x V ≤ centralizer (V : Set G) := by
  intro e he
  rw [mem_centralizer_iff]
  intro v hv
  exact h.EV_comm (V_le_EV hv) he

theorem E_le_T : EV x V ≤ T := by
  intro e he
  have : e ∈ T ⊓ centralizer (EV x V : Set G) := by rw [h.E_cent]; exact he
  exact this.1

theorem cent_V_cent_E {t : G} (ht : t ∈ T) (htC : t ∈ centralizer (V : Set G)) :
    t ∈ centralizer (EV x V : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  have hxt : x * t = t * x := mem_centralizer_iff.1 (h.T_sylow.1 ht) x rfl
  have hvt : ∀ v ∈ V, v * t = t * v := fun v hv => mem_centralizer_iff.1 htC v hv
  obtain ⟨v, hv, he' | he'⟩ := (h.mem_EV).1 he <;> rw [he']
  · exact hvt v hv
  · calc v * x * t = v * (x * t) := by group
      _ = v * (t * x) := by rw [hxt]
      _ = (v * t) * x := by group
      _ = (t * v) * x := by rw [hvt v hv]
      _ = t * (v * x) := by group

theorem T_inf_C : T ⊓ centralizer (V : Set G) = EV x V := by
  apply le_antisymm
  · intro t ht
    have : t ∈ T ⊓ centralizer (EV x V : Set G) := ⟨ht.1, h.cent_V_cent_E ht.1 ht.2⟩
    rwa [h.E_cent] at this
  · intro e he
    exact ⟨h.E_le_T he, h.E_le_C he⟩

theorem cent_E_le [Finite G] {P : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hPC : P ≤ centralizer (EV x V : Set G)) : P ≤ EV x V := by
  obtain ⟨P₁, hP₁, hPP₁⟩ := SylowIn.exists_ge hPC hP
  obtain ⟨c, hc, hcP⟩ := SylowIn.conj (h.E_sylow : SylowIn 2 (EV x V) _) hP₁
  refine hPP₁.trans fun g hg => ?_
  have h1 : c⁻¹ * g * c ∈ EV x V := (hcP g).1 hg
  have h2 : c * (c⁻¹ * g * c) = (c⁻¹ * g * c) * c := (mem_centralizer_iff.1 hc _ h1).symm
  have : g = c⁻¹ * g * c := by
    calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
      _ = (c⁻¹ * g * c) * c * c⁻¹ := by rw [h2]
      _ = c⁻¹ * g * c := by group
  rw [this]; exact h1

end Out12

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

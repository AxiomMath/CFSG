module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec123_image_alt {H X : Subgroup G} (hXH : X ≤ H) (Θ : ↥H →* Equiv.Perm (Fin 5))
    (hker : ∀ x : ↥H, (x : G) ∈ X → Θ x = 1 → x = 1)
    (hsurj : ∀ σ ∈ alternatingGroup (Fin 5), ∃ x : ↥H, (x : G) ∈ X ∧ Θ x = σ)
    (hX : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) :
    ∀ x : ↥H, (x : G) ∈ X → Θ x ∈ alternatingGroup (Fin 5) := by
  let ψ : ↥X →* Equiv.Perm (Fin 5) := Θ.comp (Subgroup.inclusion hXH)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxH : Subgroup.inclusion hXH x = 1 :=
      hker (Subgroup.inclusion hXH x) (by simpa using x.2) hx
    refine Subtype.ext ?_
    have h1 : ((Subgroup.inclusion hXH x : ↥H) : G) = 1 := by rw [hxH]; rfl
    rwa [Subgroup.coe_inclusion] at h1
  have hle : alternatingGroup (Fin 5) ≤ ψ.range := by
    intro σ hσ
    obtain ⟨x, hxX, hx⟩ := hsurj σ hσ
    exact ⟨⟨(x : G), hxX⟩, by
      change Θ (Subgroup.inclusion hXH ⟨(x : G), hxX⟩) = σ
      rw [show Subgroup.inclusion hXH ⟨(x : G), hxX⟩ = x from Subtype.ext rfl, hx]⟩
  have hcardψ : Nat.card ↥X = Nat.card ↥ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv
  have hcardAlt : Nat.card ↥X = Nat.card ↥(alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := hX
    exact Nat.card_congr e.toEquiv
  have hcard : Nat.card ↥ψ.range = Nat.card ↥(alternatingGroup (Fin 5)) := by
    rw [← hcardψ, hcardAlt]
  have heq : alternatingGroup (Fin 5) = ψ.range :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  intro x hxX
  rw [heq]
  exact ⟨⟨(x : G), hxX⟩, by
    change Θ (Subgroup.inclusion hXH ⟨(x : G), hxX⟩) = Θ x
    rw [show Subgroup.inclusion hXH ⟨(x : G), hxX⟩ = x from Subtype.ext rfl]⟩

end CFSG.OddStandard.SmallF3.Omega

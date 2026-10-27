module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrCore

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open scoped commutatorElement

variable {A B : Type*} [Group A] [Group B] (ρ : A →* B)

theorem IrrAct.map {y : A} {U Z : Subgroup A} (h : IrrAct y U Z)
    (hyU : y ∈ Subgroup.normalizer (U : Set A)) :
    IrrAct (ρ y) (U.map ρ) (Z.map ρ) := by
  refine ⟨Subgroup.map_mono h.1, fun W' hZW hWU hyW => ?_⟩
  set W : Subgroup A := U ⊓ W'.comap ρ with hW
  have hyW' : y ∈ Subgroup.normalizer (W'.comap ρ : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := Subgroup.mem_normalizer_iff.1 hyW (ρ x)
    simpa [Subgroup.mem_comap, map_mul, map_inv] using this
  have hyW2 : y ∈ Subgroup.normalizer (W : Set A) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hyU, hyW'⟩
  have hZW' : Z ≤ W := fun z hz => ⟨h.1 hz, hZW (Subgroup.mem_map_of_mem ρ hz)⟩
  have hWU' : W ≤ U := inf_le_left
  have hWmap : W.map ρ = W' := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := hWU hx
      exact ⟨u, ⟨hu, hx⟩, rfl⟩
  rcases h.2 W hZW' hWU' hyW2 with h1 | h1
  · left
    rw [← hWmap, h1]
  · right
    rw [← hWmap, h1]

theorem NeedsThree.map {U Z : Subgroup A} (h : NeedsThree U Z) (hker : U ⊓ ρ.ker ≤ Z)
    (hZU : Z ≤ U) : NeedsThree (U.map ρ) (Z.map ρ) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ heq
  refine h a ha b hb (le_antisymm (sup_le ?_ hZU) ?_)
  · exact (Subgroup.closure_le U).2 (by
      rintro x (rfl | rfl)
      · exact ha
      · exact hb)
  · intro u hu
    have h1 : ρ u ∈ (Subgroup.closure {a, b} ⊔ Z).map ρ := by
      rw [Subgroup.map_sup, MonoidHom.map_closure]
      have : ρ '' ({a, b} : Set A) = {ρ a, ρ b} := by simp
      rw [this, heq]
      exact Subgroup.mem_map_of_mem ρ hu
    obtain ⟨w, hw, hwu⟩ := h1
    have hwU : w ∈ U := by
      have : w ∈ Subgroup.closure {a, b} ⊔ Z := hw
      refine (sup_le ((Subgroup.closure_le U).2 ?_) hZU) this
      rintro x (rfl | rfl)
      · exact ha
      · exact hb
    have hmem : w⁻¹ * u ∈ Z := hker ⟨U.mul_mem (U.inv_mem hwU) hu,
      MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hwu, inv_mul_cancel])⟩
    have : u = w * (w⁻¹ * u) := by group
    rw [this]
    exact mul_mem hw (Subgroup.mem_sup_right hmem)

end CFSG.AGLEmbedding.ParabAutIrr

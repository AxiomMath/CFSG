module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.TBLit

section Conj

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_map_conj (B : Subgroup G) {t : G} (ht : t ∈ B) (φ : G) :
    oddCoreIn (B.map (MulAut.conj φ).toMonoidHom) (φ * t * φ⁻¹) =
      (oddCoreIn B t).map (MulAut.conj φ).toMonoidHom := by
  have hf₁ : Function.Injective B.subtype := Subtype.val_injective
  set f₂ : ↥B →* G := (MulAut.conj φ).toMonoidHom.comp B.subtype with hf₂
  have hf₂i : Function.Injective f₂ := fun a b h =>
    hf₁ ((MulAut.conj φ).injective h)
  have h1 := map_oddCentralizerCore_of_injective hf₁ (⟨t, ht⟩ : ↥B)
  have h2 := map_oddCentralizerCore_of_injective hf₂i (⟨t, ht⟩ : ↥B)
  rw [Subgroup.range_subtype] at h1
  have hr : f₂.range = B.map (MulAut.conj φ).toMonoidHom := by
    rw [hf₂, MonoidHom.range_comp, Subgroup.range_subtype]
  have hft : f₂ ⟨t, ht⟩ = φ * t * φ⁻¹ := rfl
  rw [hr, hft] at h2
  have h3 : oddCoreIn B t = (oddCentralizerCore (⟨t, ht⟩ : ↥B)).map B.subtype := h1.symm
  rw [← h2, h3]
  conv_rhs => rw [Subgroup.map_map]

end Conj

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

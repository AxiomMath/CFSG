module

public import CFSG.GH74.GLS.C3.Layer1.Thm1AutA7

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

@[expose] def OmegaData (Kb : Type) [Group Kb] (σ : MulAut Kb) : Prop :=
  ∃ (C : Type) (_ : Group C) (_ : IsCyclic C) (ω : MulAut Kb →* C),
    (∀ a ∈ innAut Kb, ω a = 1) ∧ ω σ ≠ 1 ∧
    ∀ a : MulAut Kb, σ * a = a * σ → ω a = 1 → a ∈ innAut Kb

theorem omegaData_of_isFAut {Kb : Type} [Group Kb] [Finite Kb] {σ : MulAut Kb}
    (hσ2 : orderOf σ = 2) (h : P34.IsFAutL2A7 Kb σ) : OmegaData Kb σ := by
  obtain ⟨hne, ⟨F, _, _, e, -, hσ⟩ | ⟨⟨e7⟩, hσ⟩⟩ := h
  · have := IVK.ringAut_isCyclic F
    obtain ⟨τ, rfl⟩ := hσ
    have hτ2 : orderOf τ = 2 := by
      rw [← orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) τ]
      exact hσ2
    refine ⟨F ≃+* F, inferInstance, this, fieldProj e, ?_, ?_, ?_⟩
    · intro a ha
      exact (mem_innDiagSub_iff e a).1 (innAut_le_innDiagSub e ha)
    · rw [fieldProj_fieldAutHom]
      intro h1
      apply hne
      rw [h1, map_one]
    · intro a hac hωa
      have hD : a ∈ innDiagSub e := (mem_innDiagSub_iff e a).2 hωa
      exact centralizer_fieldAut_le_innAut e τ (by rw [hτ2]; exact even_two)
        ⟨Subgroup.mem_centralizer_singleton_iff.2 hac.symm, hD⟩
  · have hsign : ∀ w : MulAut Kb, w ∈ innAut Kb ↔ Equiv.Perm.sign (psiEquiv e7 w) = 1 := by
      intro w
      have h1 : psiEquiv e7 w ∈ (innAut Kb).map (psiEquiv e7).toMonoidHom ↔ w ∈ innAut Kb :=
        Subgroup.mem_map_iff_mem (psiEquiv e7).injective
      rw [← h1, psi_map_innAut e7, Equiv.Perm.mem_alternatingGroup]
    refine ⟨ℤˣ, inferInstance, inferInstance, Equiv.Perm.sign.comp (psiEquiv e7).toMonoidHom,
      ?_, ?_, ?_⟩
    · intro a ha
      exact (hsign a).1 ha
    · intro h1
      exact hσ ((hsign σ).2 h1)
    · intro a _ hωa
      exact (hsign a).2 hωa

end CFSG.GH74.GLS.C3.Layer1.Thm1

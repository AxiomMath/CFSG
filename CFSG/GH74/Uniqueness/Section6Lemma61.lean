module

public import CFSG.GH74.Uniqueness.Section6Defs
public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Lemma61

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.exists_conj_inf_of_mem (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) {y₁ y₂ : X} (hy₁ : y₁ ∈ Z)
    (hy₁M : y₁ ∈ M) (hy₂ : y₂ ∈ Z) (hy₂M : y₂ ∈ M) :
    ∃ i ∈ M ⊓ conjugate M t, i⁻¹ * y₁ * i = y₂ := by
  obtain ⟨x, hx, hxy⟩ := ((h.prop36c hZ ht htM).1 y₁ ⟨hy₁, hy₁M⟩).surjOn
    (show y₂ ∈ Z ∩ (M : Set X) from ⟨hy₂, hy₂M⟩)
  exact ⟨x, pPrimeCoreIn_le _ hx.1, hxy⟩

theorem IsProductDisconnected.exists_conj_inf_omega (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {β γ : Subgroup X} (hβ : β ∈ omega M) (hγ : γ ∈ omega M)
    (hβγ : β ≠ γ) {y₁ y₂ : X} (hy₁ : y₁ ∈ Z) (hy₁β : y₁ ∈ β) (hy₂ : y₂ ∈ Z) (hy₂β : y₂ ∈ β) :
    ∃ i ∈ β ⊓ γ, i⁻¹ * y₁ * i = y₂ := by
  obtain ⟨g, rfl⟩ := hβ
  obtain ⟨t, ht, rfl⟩ := h.exists_swap hZ ⟨g, rfl⟩ hγ
  exact (h.conjugate_point hZ g).exists_conj_inf_of_mem hZ ht
    ((h.conjugate_ne_iff ⟨g, rfl⟩).mp (Ne.symm hβγ)) hy₁ hy₁β hy₂ hy₂β

theorem IsProductDisconnected.transitiveOnS_of_doublyTransitive (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (hD : DoublyTransitive M) : TransitiveOnS Z M := by
  rintro γ₁ δ₁ s₁ γ₂ δ₂ s₂ ⟨hγ₁, hδ₁, hs₁, hs₁γ, hne₁⟩ ⟨hγ₂, hδ₂, hs₂, hs₂γ, hne₂⟩
  obtain ⟨g, hg1, hg2⟩ := hD γ₁ hγ₁ δ₁ hδ₁ hne₁ γ₂ hγ₂ δ₂ hδ₂ hne₂
  have hs₁' : g⁻¹ * s₁ * g ∈ Z := hZ.2 s₁ hs₁ g
  have hs₁'γ : conjugate γ₂ (g⁻¹ * s₁ * g) = γ₂ := by
    rw [← hg1, conjugate_conjugate, show g * (g⁻¹ * s₁ * g) = s₁ * g by group,
      ← conjugate_conjugate, hs₁γ]
  obtain ⟨i, hi, hi'⟩ := h.exists_conj_inf_omega hZ hγ₂ hδ₂ hne₂ hs₁'
    ((h.conjugate_eq_iff_mem hγ₂).mp hs₁'γ) hs₂ ((h.conjugate_eq_iff_mem hγ₂).mp hs₂γ)
  refine ⟨g * i, ?_, ?_, ?_⟩
  · rw [← conjugate_conjugate, hg1]
    exact (h.conjugate_eq_iff_mem hγ₂).mpr (Subgroup.mem_inf.mp hi).1
  · rw [← conjugate_conjugate, hg2]
    exact (h.conjugate_eq_iff_mem hδ₂).mpr (Subgroup.mem_inf.mp hi).2
  · calc (g * i)⁻¹ * s₁ * (g * i) = i⁻¹ * (g⁻¹ * s₁ * g) * i := by group
      _ = s₂ := hi'

theorem ZDSetup.lemma61a (S : ZDSetup X Z M) : Lemma61aStmt Z M :=
  fun hD => S.prodDisc.transitiveOnS_of_doublyTransitive S.invariant hD

end Lemma61

end CFSG.GH74.Uniqueness

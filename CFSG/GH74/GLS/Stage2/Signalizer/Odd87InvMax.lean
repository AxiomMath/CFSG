module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem center_eq_bot_of_mulEquiv_target {Y Γ : Type} [Group Y] [Group Γ] (ψ : Y ≃* Γ) (h : center Γ = ⊥) :
    center Y = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hmem : ψ x ∈ center Γ := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := Subgroup.mem_center_iff.mp hx (ψ.symm y)
    have h2 := congrArg ψ h1
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2
  rw [h] at hmem
  exact Subgroup.mem_bot.mpr (ψ.injective (by rw [Subgroup.mem_bot.mp hmem, map_one]))

theorem isSection_congr_source {Y Y' B : Type} [Group Y] [Group Y'] [Group B] (e : Y ≃* Y')
    (h : IsSection Y' B) : IsSection Y B := by
  obtain ⟨U, φ, hφ⟩ := h
  exact ⟨U, e.symm.toMonoidHom.comp φ, e.symm.surjective.comp hφ⟩

theorem KindFactor.of_equiv {k : Kind} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : KindFactor k Y') : KindFactor k Y := by
  cases k with
  | g2 =>
    obtain ⟨F, hF, hFin, hP, ⟨e'⟩⟩ := h
    exact ⟨F, hF, hFin, hP, ⟨e.trans e'⟩⟩
  | psp4 =>
    obtain ⟨F, hF, hFin, hP, ⟨e'⟩⟩ := h
    exact ⟨F, hF, hFin, hP, ⟨e.trans e'⟩⟩
  | l4 ε =>
    obtain ⟨F, hF, hFin, hP, ⟨e'⟩⟩ := h
    exact ⟨F, hF, hFin, hP, ⟨e.trans e'⟩⟩
  | m12 => exact h
  | mcl =>
    obtain ⟨n, hn1, hn2, hs⟩ := h
    exact ⟨n, hn1, hn2, isSection_congr_source e hs⟩
  | ly =>
    obtain ⟨n, hn1, hn2, hs⟩ := h
    exact ⟨n, hn1, hn2, isSection_congr_source e hs⟩

theorem comm_of_isCyclic_group {E : Type} [Group E] (h : IsCyclic E) (a b : E) : a * b = b * a := by
  obtain ⟨g, hg⟩ := h.exists_generator
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  exact (Commute.zpow_zpow_self g m n).eq

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

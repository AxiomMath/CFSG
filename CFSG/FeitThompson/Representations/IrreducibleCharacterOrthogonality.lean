module

import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
import CFSG.FeitThompson.Representations.CharInnerProductIntertwiners
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import Mathlib.Analysis.Complex.Polynomial.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module CategoryTheory

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

open scoped Classical in
theorem cfInner_character_character [Fintype G] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [ρ.IsIrreducible] [σ.IsIrreducible] :
    cfInner σ.character ρ.character = if Nonempty (ρ.Equiv σ) then 1 else 0 := by
  rw [cfInner_character_eq_finrank_intertwiningMap,
    finrank_intertwiningMap_of_isIrreducible ρ σ]
  split <;> simp

theorem nonempty_equiv_iff_character_eq [Finite G] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [ρ.IsIrreducible] [σ.IsIrreducible] :
    Nonempty (ρ.Equiv σ) ↔ ρ.character = σ.character := by
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨fun ⟨e⟩ => Representation.char_iso e, fun h => ?_⟩
  by_contra hne
  have h0 : cfInner σ.character ρ.character = 0 := by
    rw [cfInner_character_character]; exact if_neg hne
  have h1 : cfInner ρ.character ρ.character = 1 := by
    rw [cfInner_character_character]; exact if_pos ⟨Representation.Equiv.refl ρ⟩
  rw [← h, h1] at h0
  exact one_ne_zero h0

theorem character_ne_character_of_isEmpty_equiv [Finite G] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [ρ.IsIrreducible] [σ.IsIrreducible]
    (h : IsEmpty (ρ.Equiv σ)) : ρ.character ≠ σ.character :=
  fun he => (not_nonempty_iff.2 h) ((nonempty_equiv_iff_character_eq ρ σ).2 he)

open scoped Classical in
theorem cfInner_eq_ite_of_mem_Irr [Fintype G] {χ ψ : G → ℂ} (hχ : χ ∈ Irr G) (hψ : ψ ∈ Irr G) :
    cfInner χ ψ = if χ = ψ then 1 else 0 := by
  obtain ⟨X, hX, rfl⟩ := mem_Irr.1 hχ
  obtain ⟨Y, hY, rfl⟩ := mem_Irr.1 hψ
  have := hX
  have := hY
  rw [show (FDRep.character X) = Representation.character X.ρ from rfl,
      show (FDRep.character Y) = Representation.character Y.ρ from rfl,
      cfInner_character_character Y.ρ X.ρ]
  simp [nonempty_equiv_iff_character_eq, eq_comm]

theorem cfInner_self_of_mem_Irr [Fintype G] {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    cfInner χ χ = 1 := by
  classical
  rw [cfInner_eq_ite_of_mem_Irr hχ hχ, if_pos rfl]

theorem cfInner_eq_zero_of_mem_Irr [Fintype G] {χ ψ : G → ℂ} (hχ : χ ∈ Irr G) (hψ : ψ ∈ Irr G)
    (h : χ ≠ ψ) : cfInner χ ψ = 0 := by
  classical
  rw [cfInner_eq_ite_of_mem_Irr hχ hψ, if_neg h]

open scoped Classical in
theorem cfInner_character_character_fdRep [Fintype G] (X Y : FDRep ℂ G) [Simple X] [Simple Y] :
    cfInner Y.character X.character = if Nonempty (X ≅ Y) then 1 else 0 := by
  rw [cfInner_character_eq_finrank_hom, FDRep.finrank_hom_simple_simple]
  split <;> simp

theorem nonempty_iso_iff_character_eq [Finite G] (X Y : FDRep ℂ G) [Simple X] [Simple Y] :
    Nonempty (X ≅ Y) ↔ X.character = Y.character := by
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨fun ⟨e⟩ => FDRep.char_iso e, fun h => ?_⟩
  by_contra hne
  have h0 : cfInner Y.character X.character = 0 := by
    rw [cfInner_character_character_fdRep]; exact if_neg hne
  have h1 : cfInner X.character X.character = 1 := by
    rw [cfInner_character_character_fdRep]; exact if_pos ⟨Iso.refl X⟩
  rw [← h, h1] at h0
  exact one_ne_zero h0

end CFSG.FeitThompson

module

public import Mathlib.RepresentationTheory.Maschke

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Representation

variable {k A V : Type*} [Field k] [Group A] [Finite A] [AddCommGroup V] [Module k V]

theorem exists_invariant_isCompl_of_natCard_ne_zero (hA : (Nat.card A : k) ≠ 0)
    (ρ : Representation k A V) (W : Submodule k V)
    (hW : ∀ a : A, ∀ v ∈ W, ρ a v ∈ W) :
    ∃ U : Submodule k V, (∀ a : A, ∀ v ∈ U, ρ a v ∈ U) ∧ IsCompl W U := by
  have : NeZero ((Nat.card A : k)) := ⟨hA⟩
  obtain ⟨U, hU⟩ := exists_isCompl (⟨W, hW⟩ : Subrepresentation ρ)
  have htop : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := (rfl)
  have hbot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := (rfl)
  refine ⟨U.toSubmodule, U.apply_mem_toSubmodule, ?_, ?_⟩
  · have h := congrArg Subrepresentation.toSubmodule hU.inf_eq_bot
    rw [Subrepresentation.toSubmodule_inf, hbot] at h
    simpa [disjoint_iff] using h
  · have h := congrArg Subrepresentation.toSubmodule hU.sup_eq_top
    rw [Subrepresentation.toSubmodule_sup, htop] at h
    simpa [codisjoint_iff] using h

theorem exists_invariant_isCompl_of_generalLinearGroup (hA : (Nat.card A : k) ≠ 0)
    (ρ : A →* LinearMap.GeneralLinearGroup k V) (W : Submodule k V)
    (hW : ∀ a : A, ∀ v ∈ W, (ρ a : V →ₗ[k] V) v ∈ W) :
    ∃ U : Submodule k V, (∀ a : A, ∀ v ∈ U, (ρ a : V →ₗ[k] V) v ∈ U) ∧ IsCompl W U :=
  exists_invariant_isCompl_of_natCard_ne_zero hA ((Units.coeHom (V →ₗ[k] V)).comp ρ) W hW

theorem exists_invariant_sup_eq_top_inf_eq_bot_of_generalLinearGroup (hA : (Nat.card A : k) ≠ 0)
    (ρ : A →* LinearMap.GeneralLinearGroup k V) (W : Submodule k V)
    (hW : ∀ a : A, ∀ v ∈ W, (ρ a : V →ₗ[k] V) v ∈ W) :
    ∃ U : Submodule k V,
      (∀ a : A, ∀ v ∈ U, (ρ a : V →ₗ[k] V) v ∈ U) ∧ W ⊔ U = ⊤ ∧ W ⊓ U = ⊥ := by
  obtain ⟨U, hU, hc⟩ := exists_invariant_isCompl_of_generalLinearGroup hA ρ W hW
  exact ⟨U, hU, hc.sup_eq_top, hc.inf_eq_bot⟩

end CFSG.FeitThompson

module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.CategoryTheory.Category.Init

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Representation

variable {G k V : Type*} [Monoid G] [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible]

theorem Representation.IsIrreducible.exists_eq_smul_one_of_commute (T : Module.End k V)
    (hT : ∀ g : G, Commute T (ρ g)) : ∃ c : k, T = c • (1 : Module.End k V) := by
  have hT' : ∀ g : G, T ∘ₗ ρ g = ρ g ∘ₗ T := fun g => hT g
  obtain ⟨c, hc⟩ :=
    (_root_.Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (⟨T, hT'⟩ : ρ.IntertwiningMap ρ)
  refine ⟨c, ?_⟩
  have h := congrArg _root_.Representation.IntertwiningMap.toLinearMap hc
  simp at h
  ext v
  simpa using congrArg (fun f => f v) h.symm

theorem Representation.IsIrreducible.exists_forall_apply_eq_smul_of_commute (T : Module.End k V)
    (hT : ∀ g : G, Commute T (ρ g)) : ∃ c : k, ∀ v : V, T v = c • v := by
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.exists_eq_smul_one_of_commute ρ T hT
  exact ⟨c, fun v => by rw [hc]; simp⟩

theorem Representation.IsIrreducible.centralizer_range_eq_range_algebraMap :
    Set.centralizer (Set.range ρ) = Set.range (algebraMap k (Module.End k V)) := by
  ext T
  constructor
  · intro hT
    obtain ⟨c, hc⟩ :=
      Representation.IsIrreducible.exists_eq_smul_one_of_commute ρ T fun g => (hT _ ⟨g, rfl⟩).symm
    exact ⟨c, by simp [hc, Algebra.algebraMap_eq_smul_one]⟩
  · rintro ⟨c, rfl⟩ _ ⟨g, rfl⟩
    exact (Algebra.commutes c (ρ g)).symm

end CFSG.FeitThompson

module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Order.SupIndep

public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.IndependentFamilyRemoveZero

theorem remove_zero {R : Type*} {V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    {I : Type*} (f : I → Submodule R V) (J : Set I) (z : I) (hz : z ∉ J)
    (hind : iSupIndep (fun i : (insert z J : Set I) => f i)) (hfz : f z = ⊥) :
    iSupIndep (fun i : J => f i) ∧
      (⨆ i : J, f i) = ⨆ i : (insert z J : Set I), f i := by
  refine ⟨?_, ?_⟩
  · exact hind.comp (f := fun i : J => (⟨i.1, Set.mem_insert_of_mem z i.2⟩ : (insert z J : Set I)))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
  · apply le_antisymm
    · exact iSup_le fun i => le_iSup (fun i : (insert z J : Set I) => f i)
        ⟨i.1, Set.mem_insert_of_mem z i.2⟩
    · refine iSup_le fun i => ?_
      rcases i with ⟨i, hi⟩
      rcases hi with rfl | hi
      · simp [hfz]
      · exact le_iSup (fun i : J => f i) ⟨i, hi⟩

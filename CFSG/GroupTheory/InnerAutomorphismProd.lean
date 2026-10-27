module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.GroupTheory

theorem mem_inner_of_mulEquiv_prod {X A B : Type*} [Group X] [Group A] [Group B]
    (e : X ≃* A × B) (ρ : MulAut X) (α : MulAut A) (β : MulAut B)
    (heρ : ∀ u : X, e (ρ u) = (α (e u).1, β (e u).2))
    (hα : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner A)
    (hβ : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner B) :
    ρ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
  obtain ⟨a, ha⟩ := hα
  obtain ⟨b, hb⟩ := hβ
  refine ⟨e.symm (a, b), ?_⟩
  ext u
  apply e.injective
  rw [MulAut.conj_apply, heρ, map_mul, map_mul, e.apply_symm_apply]
  rw [← ha, ← hb]
  ext <;> simp [MulAut.conj_apply]

end CFSG.GroupTheory

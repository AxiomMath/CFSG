module

public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.GroupTheory

theorem selfCentralizing_map_mulEquiv {p : ℕ} {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') {E : Subgroup G}
    (h : ∀ x : G, (∀ a ∈ E, x * a = a * x) → x ^ p = 1 → x ∈ E) :
    ∀ x : G', (∀ b ∈ E.map e.toMonoidHom, x * b = b * x) → x ^ p = 1 →
      x ∈ E.map e.toMonoidHom := by
  intro x hx hxp
  obtain ⟨y, rfl⟩ : ∃ y, e y = x := ⟨e.symm x, e.apply_symm_apply x⟩
  refine Subgroup.mem_map_of_mem e.toMonoidHom (h y (fun a ha => ?_) ?_)
  · have h1 := hx (e a) (Subgroup.mem_map_of_mem e.toMonoidHom ha)
    exact e.injective (by rw [map_mul, map_mul]; exact h1)
  · exact e.injective (by rw [map_pow, hxp, map_one])

end CFSG.GroupTheory

end

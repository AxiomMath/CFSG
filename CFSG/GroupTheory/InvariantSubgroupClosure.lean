module

public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem eq_or_eq_of_le_normalizer_of_closure_conj_eq {M V₀ V : Subgroup G}
    (hgen : ∀ v ∈ V, v ∉ V₀ → Subgroup.closure {x : G | ∃ m ∈ M, x = m * v * m⁻¹} = V)
    {U : Subgroup G} (hUV : U ≤ V) (hV₀U : V₀ ≤ U)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) : U = V₀ ∨ U = V := by
  by_cases hEq : U = V₀
  · exact Or.inl hEq
  · refine Or.inr ?_
    have hnot : ¬ U ≤ V₀ := fun hle => hEq (le_antisymm hle hV₀U)
    obtain ⟨u, huU, huV₀⟩ :=
      Set.not_subset.mp (show ¬ (U : Set G) ⊆ (V₀ : Set G) from hnot)
    have hcl := hgen u (hUV huU) huV₀
    have hle : Subgroup.closure {x : G | ∃ m ∈ M, x = m * u * m⁻¹} ≤ U := by
      rw [Subgroup.closure_le]
      rintro x ⟨m, hmM, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hMU hmM) u).mp huU
    rw [hcl] at hle
    exact le_antisymm hUV hle

end CFSG.GroupTheory

module

public import CFSG.LargeExtraspecial.A2ModLines

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_point_le_or_exists_plane_ge {𝓕 : Set (Submodule K V)} (hne : 𝓕.Nonempty)
    (h2 : ∀ A ∈ 𝓕, finrank K A = 2)
    (h1 : ∀ A ∈ 𝓕, ∀ A' ∈ 𝓕, A ≠ A' → finrank K ↥(A ⊓ A') = 1) :
    (∃ P : Submodule K V, finrank K P = 1 ∧ ∀ A ∈ 𝓕, P ≤ A) ∨
      ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ A ∈ 𝓕, A ≤ U := by
  have hmeet : ∀ L ∈ 𝓕, ∀ M ∈ 𝓕, L ⊓ M ≠ ⊥ := by
    intro L hL M hM h
    by_cases hLM : L = M
    · subst hLM
      rw [inf_idem] at h
      have := h2 L hL
      rw [h, finrank_bot] at this
      omega
    · have := h1 L hL M hM hLM
      rw [h, finrank_bot] at this
      omega
  rcases LargeExtraspecial.A2Mod.concurrent_or_coplanar h2 hmeet with ⟨p, hp0, hp⟩ | ⟨W, hW3, hW⟩
  · refine Or.inl ⟨Submodule.span K {p}, finrank_span_singleton hp0, fun A hA => ?_⟩
    rw [Submodule.span_singleton_le_iff_mem]
    exact hp A hA
  by_cases hW3' : finrank K W = 3
  · exact Or.inr ⟨W, hW3', hW⟩
  obtain ⟨A₀, hA₀⟩ := hne
  have hA₀W : A₀ = W :=
    Submodule.eq_of_le_of_finrank_le (hW A₀ hA₀) (by rw [h2 A₀ hA₀]; omega)
  have hbot : A₀ ≠ ⊥ := fun h => by
    have := h2 A₀ hA₀
    rw [h, finrank_bot] at this
    omega
  obtain ⟨p, hpA₀, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine Or.inl ⟨Submodule.span K {p}, finrank_span_singleton hp0, fun A hA => ?_⟩
  have hAW : A = W :=
    Submodule.eq_of_le_of_finrank_le (hW A hA) (by rw [h2 A hA]; omega)
  rw [Submodule.span_singleton_le_iff_mem, hAW, ← hA₀W]
  exact hpA₀

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1

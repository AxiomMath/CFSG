module

public import CFSG.Combinatorics.AperiodicSixteenGraphSupport

public section

open Finset

namespace CFSG.Combinatorics.AperiodicSixteenGraph

theorem aperiodic_sixteen_graph_distances_and_three_paths :
    let path : K → K → K → K → Prop := fun x₀ x₁ x₂ x₃ =>
      T.Adj x₀ x₁ ∧ T.Adj x₁ x₂ ∧ T.Adj x₂ x₃ ∧ [x₀, x₁, x₂, x₃].Nodup
    T.Connected ∧ T.IsBipartite ∧ (∀ g (p : T.Walk g g), p.IsCycle → 6 ≤ p.length) ∧
      (univ.filter fun g => T.dist o g = 0).card = 1 ∧
      (univ.filter fun g => T.dist o g = 1).card = 3 ∧
      (univ.filter fun g => T.dist o g = 2).card = 6 ∧
      (univ.filter fun g => T.dist o g = 3).card = 5 ∧
      (univ.filter fun g => T.dist o g = 4).card = 1 ∧ (∀ g, T.dist o g ≤ 4) ∧
      (∀ g h, T.dist g h = 4 ↔ h = τ g) ∧
      Function.Involutive τ ∧ (∀ g h, T.Adj (τ g) (τ h) ↔ T.Adj g h) ∧
      (∀ g i, τ (g * s i) = τ g * s i) ∧
      (∀ g (i j k : Fin 3), i ≠ j → j ≠ k → i ≠ k →
        g * s i * s j * s i = τ (g * s j) ∧ g * s k * s j * s k = τ (g * s j) ∧
        g * s i ≠ g * s k ∧
        {m : K × K | path g m.1 m.2 (τ (g * s j))} =
          {(g * s i, g * s i * s j), (g * s k, g * s k * s j)}) ∧
      (∀ g (i j k : Fin 3), i ≠ j → j ≠ k → i ≠ k →
        g * s j * s k * s i = g * s i * s j * s k ∧ g * s k * s i * s j = g * s i * s j * s k ∧
        g * s i ≠ g * s j ∧ g * s j ≠ g * s k ∧ g * s i ≠ g * s k ∧
        {m : K × K | path g m.1 m.2 (g * s i * s j * s k)} =
          {(g * s i, g * s i * s j), (g * s j, g * s j * s k), (g * s k, g * s k * s i)} ∧
        g * s i * s k * s j = g * s k * s j * s i ∧ g * s j * s i * s k = g * s k * s j * s i ∧
        g * s k * s j * s i ≠ g * s i * s j * s k) ∧
      ∀ x₀ x₁ x₂ x₃, path x₀ x₁ x₂ x₃ → ∃ a b c : Fin 3,
        x₁ = x₀ * s a ∧ x₂ = x₁ * s b ∧ x₃ = x₂ * s c ∧ a ≠ b ∧ b ≠ c ∧
        ((a ≠ c ∧ {m : K × K | path x₀ m.1 m.2 x₃} =
            {(x₀ * s a, x₀ * s a * s b), (x₀ * s b, x₀ * s b * s c),
              (x₀ * s c, x₀ * s c * s a)}) ∨
          (a = c ∧ ∃ d, d ≠ a ∧ d ≠ b ∧ x₃ = τ (x₀ * s b) ∧
            {m : K × K | path x₀ m.1 m.2 x₃} =
              {(x₀ * s a, x₀ * s a * s b), (x₀ * s d, x₀ * s d * s b)})) := by
  intro path
  have hne : ∀ (g : K) {a b : Fin 3}, a ≠ b → g * s a ≠ g * s b :=
    fun g a b hab h => hab (s_injective (mul_left_cancel h))
  obtain ⟨h0, h1, h2, h3, h4, hle⟩ := card_sphere
  refine ⟨connected, isBipartite, fun g p hp => six_le_length_of_isCycle p hp, h0, h1, h2, h3,
    h4, hle, dist_eq_four_iff, τ_τ, fun g h => adj_τ_iff, τ_mul_s,
    fun g i j k hij hjk hik => ⟨endpoint_τ g hij, endpoint_τ g hjk.symm, hne g hik,
      paths_to_τ g hij hjk hik⟩,
    fun g i j k hij hjk hik => ⟨(endpoint_cyclic g hij hjk hik).1,
      (endpoint_cyclic g hij hjk hik).2, hne g hij, hne g hjk, hne g hik,
      paths_cyclic g hij hjk hik, endpoint_reverse g hij hjk hik⟩, ?_⟩
  intro x₀ x₁ x₂ x₃ hpath
  obtain ⟨a, b, c, hab, hbc, rfl, rfl, rfl⟩ := path_iff.mp hpath
  refine ⟨a, b, c, rfl, rfl, rfl, hab, hbc, ?_⟩
  by_cases hac : a = c
  · subst hac
    obtain ⟨d, hda, hdb⟩ := (by decide : ∀ a b : Fin 3, a ≠ b → ∃ d, d ≠ a ∧ d ≠ b) a b hab
    refine Or.inr ⟨rfl, d, hda, hdb, endpoint_τ x₀ hab, ?_⟩
    rw [endpoint_τ x₀ hab]
    exact paths_to_τ x₀ hab hdb.symm hda.symm
  · exact Or.inl ⟨hac, paths_cyclic x₀ hab hbc hac⟩

end CFSG.Combinatorics.AperiodicSixteenGraph

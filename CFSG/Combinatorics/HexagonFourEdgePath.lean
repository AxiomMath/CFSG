module

public import CFSG.Combinatorics.HexagonFourEdgePathCompletion

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers

namespace CFSG.Combinatorics.HexagonFourEdgePath

theorem opposite_four_edge_path_completion_and_six_cycle_color_counts {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (H : MooreHyp G)
    (col : G.Coloring Bool) (w : {v : V // col v = false}) (ℓ : Fin 3 → V)
    (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    (p : Fin 3 → Fin 2 → {v : V // col v = false}) (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i))
    (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2) :
    let Γ : SimpleGraph {v : V // col v = false} := pointGraph G col
    let O : Set {v : V // col v = false} := {x | Γ.dist w x = 3}
    (∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y →
      (∀ m : V, G.Adj (x : V) m → G.Adj (y : V) m →
        G.neighborFinset m = {(x : V), (y : V), (z x y : V)}) ∧
      (∀ t, Γ.Adj (z x y) t ∧ Γ.dist w t = 1 ↔ t = q x y) ∧ q x y = p (c x y) (ε x y)) →
    (∀ x : Fin 6 → {v : V // col v = false}, Function.Injective x → (∀ n, x n ∈ O) →
      (∀ n, Γ.Adj (x n) (x (n + 1))) →
        ∀ i : Fin 3, (univ.filter fun n => c (x n) (x (n + 1)) = i).card = 2) ∧
    (∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      ∀ v₀ ∈ O, ∀ v₁ ∈ O, ∀ v₂ ∈ O, ∀ v₃ ∈ O, ∀ v₄ ∈ O,
        Γ.Adj v₀ v₁ → Γ.Adj v₁ v₂ → Γ.Adj v₂ v₃ → Γ.Adj v₃ v₄ → [v₀, v₁, v₂, v₃, v₄].Nodup →
          c v₀ v₁ = i → c v₁ v₂ = j → c v₂ v₃ = k → c v₃ v₄ = i →
            ∃ u, (u ∈ O ∧ Γ.Adj v₀ u ∧ Γ.Adj v₄ u) ∧
              (∀ u' ∈ O, Γ.Adj v₀ u' → Γ.Adj v₄ u' → u' = u) ∧
              [v₀, v₁, v₂, v₃, v₄, u].Nodup ∧
              ((c v₄ u = j ∧ c u v₀ = k) ∨ (c v₄ u = k ∧ c u v₀ = j))) := by
  intro Γ O hdata
  refine ⟨fun x hx hO hadj i => six_cycle_colours H col hℓ hwℓ hpℓ hpw hp hdata hx hO hadj i,
    ?_⟩
  intro i j k hij hjk hik v₀ h₀ v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ h01 h12 h23 h34 hnd hc₀ hc₁ hc₂ hc₃
  obtain ⟨u, ⟨hu, h0u, h4u⟩, huniq, hnd6⟩ := four_path_completion H col hℓ hwℓ hpℓ hpw hp hdata
    hij hjk hik h₀ h₁ h₂ h₃ h₄ h01 h12 h23 h34 hnd hc₀ hc₁ hc₂ hc₃
  refine ⟨u, ⟨hu, h0u, h4u⟩, huniq, hnd6, ?_⟩
  have hinj : Function.Injective ![v₀, v₁, v₂, v₃, v₄, u] :=
    List.nodup_ofFn.mp (by simpa [List.ofFn_succ] using hnd6)
  have hO6 : ∀ n, (pointGraph G col).dist w (![v₀, v₁, v₂, v₃, v₄, u] n) = 3 := by
    intro n
    fin_cases n
    exacts [h₀, h₁, h₂, h₃, h₄, hu]
  have hadj6 : ∀ n, (pointGraph G col).Adj (![v₀, v₁, v₂, v₃, v₄, u] n)
      (![v₀, v₁, v₂, v₃, v₄, u] (n + 1)) := by
    intro n
    fin_cases n
    exacts [h01, h12, h23, h34, h4u, h0u.symm]
  have hcol : ∀ n : Fin 6, c (![v₀, v₁, v₂, v₃, v₄, u] n) (![v₀, v₁, v₂, v₃, v₄, u] (n + 1)) =
      ![i, j, k, i, c v₄ u, c u v₀] n := by
    intro n
    fin_cases n <;> simp [hc₀, hc₁, hc₂, hc₃]
  have hcount : ∀ i' : Fin 3, (univ.filter fun n => ![i, j, k, i, c v₄ u, c u v₀] n = i').card
      = 2 := by
    intro i'
    have h := six_cycle_colours H col hℓ hwℓ hpℓ hpw hp hdata hinj hO6 hadj6 i'
    rwa [Finset.filter_congr fun n _ => by rw [hcol n]] at h
  have key : ∀ x y i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      (univ.filter fun n => ![i, j, k, i, x, y] n = i).card = 2 →
      (univ.filter fun n => ![i, j, k, i, x, y] n = j).card = 2 →
      (x = j ∧ y = k) ∨ (x = k ∧ y = j) := by
    decide
  exact key _ _ i j k hij hjk hik (hcount i) (hcount j)

end CFSG.Combinatorics.HexagonFourEdgePath

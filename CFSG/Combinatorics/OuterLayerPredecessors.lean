module

public import CFSG.Combinatorics.OuterLayerPredecessorsGraph

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers

namespace CFSG.Combinatorics.OuterLayer

theorem outer_layer_distance_relation_recovers_predecessors {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 126)
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 3) (col : G.Coloring Bool)
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (w : {v : V // col v = false}) (ℓ : Fin 3 → V) (hℓ : Function.Injective ℓ)
    (hwℓ : ∀ i, G.Adj (w : V) (ℓ i)) (p : Fin 3 → Fin 2 → {v : V // col v = false})
    (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i)) (hpw : ∀ i e, p i e ≠ w)
    (hp : ∀ i, Function.Injective (p i)) :
    let Γ : SimpleGraph {v : V // col v = false} := pointGraph G col
    (∀ i : ℕ, (i = 1 ∨ i = 2) → ∀ x, Γ.dist w x = i →
      ∃! s : {v : V // col v = false}, Γ.dist w s = i - 1 ∧ Γ.Adj x s) ∧
    (∀ i : ℕ, (i = 1 ∨ i = 2) → ∀ x y : {v : V // col v = false}, Γ.dist w x = i →
      Γ.dist w y = i → x ≠ y →
      (OuterRel G col w i x y ↔ ∃ s : {v : V // col v = false}, Γ.dist w s = i - 1 ∧
        Γ.Adj x s ∧ Γ.Adj y s ∧ ∀ m m' : V, G.Adj (x : V) m → G.Adj (s : V) m →
          G.Adj (y : V) m' → G.Adj (s : V) m' → m ≠ m')) ∧
    (Fintype.card {s : {v : V // col v = false} // Γ.dist w s = 1} = 6 ∧
      ∃ φ : copies {s : {v : V // col v = false} // Γ.dist w s = 1}
          (SimpleGraph.completeEquipartiteGraph 2 2) ≃g outerRelGraph G col w 2,
        (∀ (s : {s : {v : V // col v = false} // Γ.dist w s = 1})
          (x : {x : {v : V // col v = false} // Γ.dist w x = 2}),
          Γ.Adj (x : {v : V // col v = false}) s ↔ ∃ a, φ (s, a) = x) ∧
        ∀ (s : {s : {v : V // col v = false} // Γ.dist w s = 1}) (j : Fin 2),
          ∃ m : V, G.Adj ((s : {v : V // col v = false}) : V) m ∧
            ∀ e, G.Adj ((φ (s, (j, e)) : {v : V // col v = false}) : V) m) ∧
    (∃ φ : SimpleGraph.completeEquipartiteGraph 3 2 ≃g outerRelGraph G col w 1,
      ∀ j e, ((φ (j, e) : {v : V // col v = false}) : V) = p j e) ∧
    ∀ i : ℕ, (i = 1 ∨ i = 2) →
      ∃ e : (outerRelGraph G col w i).ConnectedComponent ≃
          {s : {v : V // col v = false} // Γ.dist w s = i - 1},
        (∀ x : {x : {v : V // col v = false} // Γ.dist w x = i},
          Γ.Adj (x : {v : V // col v = false})
            (e ((outerRelGraph G col w i).connectedComponentMk x))) ∧
        ∀ x y : {x : {v : V // col v = false} // Γ.dist w x = i}, x ≠ y →
          (outerRelGraph G col w i).connectedComponentMk x =
            (outerRelGraph G col w i).connectedComponentMk y →
          (¬ (outerRelGraph G col w i).Adj x y ↔ ∃ m : V, ¬ IsOuterLine G col w i m ∧
            G.neighborFinset m = {((e ((outerRelGraph G col w i).connectedComponentMk x) :
              {v : V // col v = false}) : V), ((x : {v : V // col v = false}) : V),
              ((y : {v : V // col v = false}) : V)}) := by
  intro Γ
  have H : MooreHyp G := ⟨hcard, hconn, hdeg, hcyc⟩
  obtain ⟨φ₁, hφ₁⟩ := outerRelGraph_one_iso H hℓ hwℓ hpℓ hpw hp
  refine ⟨fun i hi x hx => existsUnique_pred H hi hx, fun i hi x y hx hy hxy =>
    ⟨fun hR => exists_pred_of_outerRel H hi hx hy hxy hR,
      fun ⟨s, hs, hxs, hys, hl⟩ => outerRel_of_pred H hi hx hy hs hxs hys hl⟩,
    ⟨(Fintype.card_congr φ₁.toEquiv).symm.trans (by simp), outerRelGraph_two_iso H⟩,
    ⟨φ₁, hφ₁⟩, fun i hi => outerRelGraph_components H hi⟩

end CFSG.Combinatorics.OuterLayer

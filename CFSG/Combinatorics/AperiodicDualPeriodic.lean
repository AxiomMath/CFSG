module

public import CFSG.Combinatorics.AperiodicDualPeriodicSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

theorem lines_through_an_aperiodic_point_are_dual_periodic {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (H : MooreHyp G)
    (col : G.Coloring Bool) (w : {v : V // col v = false}) (ℓ : Fin 3 → V)
    (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    (p : Fin 3 → Fin 2 → {v : V // col v = false}) (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i))
    (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2)
    (hdata : IsFrameData G col w p z q c ε)
    (r : Fin 3 → {v : V // col v = false} → {v : V // col v = false})
    (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
      (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i) :
    let Γ : SimpleGraph {v : V // col v = false} := pointGraph G col
    let O : Set {v : V // col v = false} := {x | Γ.dist w x = 3}
    let hexagon : (Fin 6 → {v : V // col v = false}) → Prop := fun x =>
      Function.Injective x ∧ (∀ n, x n ∈ O) ∧ ∀ n, Γ.Adj (x n) (x (n + 1))
    let periodic : (Fin 6 → {v : V // col v = false}) → Prop := fun x =>
      ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ ∀ n, c (x n) (x (n + 1)) = ![i, j, k, i, j, k] n
    (¬ ∃ x, hexagon x ∧ periodic x) →
      ∀ u : {v : V // dualCol col v = false}, G.Adj (w : V) u →
        let Γ' : SimpleGraph {v : V // dualCol col v = false} := pointGraph G (dualCol col)
        let O' : Set {v : V // dualCol col v = false} := {x | Γ'.dist u x = 3}
        (∃ (ℓ' : Fin 3 → V) (p' : Fin 3 → Fin 2 → {v : V // dualCol col v = false})
            (z' q' : {v : V // dualCol col v = false} → {v : V // dualCol col v = false} →
              {v : V // dualCol col v = false})
            (c' : {v : V // dualCol col v = false} → {v : V // dualCol col v = false} → Fin 3)
            (ε' : {v : V // dualCol col v = false} → {v : V // dualCol col v = false} → Fin 2),
            Function.Injective ℓ' ∧ (∀ i, G.Adj (u : V) (ℓ' i)) ∧
            (∀ i e, G.Adj (p' i e : V) (ℓ' i)) ∧ (∀ i e, p' i e ≠ u) ∧
            (∀ i, Function.Injective (p' i)) ∧ IsFrameData G (dualCol col) u p' z' q' c' ε') ∧
        ∀ (ℓ' : Fin 3 → V), Function.Injective ℓ' → (∀ i, G.Adj (u : V) (ℓ' i)) →
        ∀ (p' : Fin 3 → Fin 2 → {v : V // dualCol col v = false}),
          (∀ i e, G.Adj (p' i e : V) (ℓ' i)) → (∀ i e, p' i e ≠ u) →
          (∀ i, Function.Injective (p' i)) →
        ∀ (z' q' : {v : V // dualCol col v = false} → {v : V // dualCol col v = false} →
            {v : V // dualCol col v = false})
          (c' : {v : V // dualCol col v = false} → {v : V // dualCol col v = false} → Fin 3)
          (ε' : {v : V // dualCol col v = false} → {v : V // dualCol col v = false} → Fin 2),
          IsFrameData G (dualCol col) u p' z' q' c' ε' →
          ∃ x : Fin 6 → {v : V // dualCol col v = false},
            (Function.Injective x ∧ (∀ n, x n ∈ O') ∧ ∀ n, Γ'.Adj (x n) (x (n + 1))) ∧
            ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
              ∀ n, c' (x n) (x (n + 1)) = ![i, j, k, i, j, k] n := by
  intro Γ O hexagon periodic haper u hwu Γ' O'
  have F : IsFrame G col w ℓ p z q c ε := ⟨H, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩
  have haper' : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x :=
    fun x hx hpx => haper ⟨x, hx, hpx⟩
  exact ⟨exists_frameData H (dualCol col) u, fun ℓ' hℓ' hwℓ' p' hpℓ' hpw' hp' z' q' c' ε' hdata' =>
    exists_periodic_dual F hr haper' hwu hℓ' hwℓ' hpℓ' hpw' hp' hdata'⟩

end CFSG.Combinatorics.AperiodicOppositeComponents

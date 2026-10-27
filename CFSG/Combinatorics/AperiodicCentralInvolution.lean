module

public import CFSG.Combinatorics.AperiodicCentralInvolutionMap

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

theorem aperiodic_central_involution_extends_across_all_layers {V : Type*} [Fintype V]
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
    let σ : {v : V // col v = false} → {v : V // col v = false} := sigmaMap G col w
    (¬ ∃ x, hexagon x ∧ periodic x) →
      (∀ x ∈ O, Γ.dist x (σ x) = 3) ∧
      (∀ γ ∈ O, ∀ δ ∈ O, Γ.Adj γ δ →
        z γ δ ≠ z (σ γ) (σ δ) ∧ Γ.Adj (z γ δ) (z (σ γ) (σ δ))) ∧
      ∃ Φ : G ≃g G, (∀ v, col (Φ v) = col v) ∧ (∀ v, Φ (Φ v) = v) ∧
        (∀ x ∈ O, Φ (x : V) = (σ x : V)) ∧ Φ (w : V) = w ∧
        (∀ x : {v : V // col v = false}, Γ.dist w x = 1 → Φ (x : V) = x) ∧
        ∀ (m : V) (a t t' : {v : V // col v = false}), Γ.dist w a = 1 → Γ.dist w t = 2 →
          Γ.dist w t' = 2 → t ≠ t' → G.Adj (a : V) m → G.Adj (t : V) m → G.Adj (t' : V) m →
            Φ (t : V) = t' := by
  intro Γ O hexagon periodic σ haper
  have F : IsFrame G col w ℓ p z q c ε := ⟨H, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩
  have haper' : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x :=
    fun x hx hpx => haper ⟨x, hx, hpx⟩
  let Φ : G ≃g G := ⟨Function.Involutive.toPerm _ (incMap_incMap F hr haper'),
    fun {a b} => adj_incMap_iff F hr haper' a b⟩
  refine ⟨fun x hx => dist_sigmaMap F hr haper' hx, fun γ hγ δ hδ hγδ =>
      ⟨(adj_third_sigmaMap F hr haper' hγ hδ hγδ).ne, adj_third_sigmaMap F hr haper' hγ hδ hγδ⟩,
    Φ, col_incMap F hr haper', incMap_incMap F hr haper', fun x hx => ?_, ?_, fun x hx => ?_,
    fun m a t t' _ ht ht' htt' _ htm ht'm => ?_⟩
  ·
    show incMap G col w x = _
    rw [incMap_point, ptMap_of_three hx]
  ·
    show incMap G col w w = w
    rw [incMap_point, ptMap_of_le_one (x := w) (by simp)]
  ·
    show incMap G col w x = x
    rw [incMap_point, ptMap_of_le_one (x := x) (le_of_eq hx)]
  ·
    show incMap G col w t = t'
    have htt'' : Γ.Adj t t' := (point_adj_iff F.moore.conn col t t').mpr
      (dist_eq_two_of_adj_adj F.moore.conn col (fun h => htt' (Subtype.ext h))
        (t.2.trans t'.2.symm) htm ht'm)
    rw [incMap_point, ptMap_of_two ht, ← eq_sibling F ht ht' htt'']

end CFSG.Combinatorics.AperiodicOppositeComponents

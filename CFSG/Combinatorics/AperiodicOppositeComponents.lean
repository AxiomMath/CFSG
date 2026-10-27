module

public import CFSG.Combinatorics.AperiodicOppositeComponentsSigma

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

theorem aperiodic_point_opposite_components_and_central_involution {V : Type*} [Fintype V]
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
    let comp : (Γ.induce O).ConnectedComponent → Set {v : V // col v = false} := fun Q =>
      {x | ∃ h : x ∈ O, (Γ.induce O).connectedComponentMk ⟨x, h⟩ = Q}
    let path : {v : V // col v = false} → {v : V // col v = false} →
        {v : V // col v = false} → {v : V // col v = false} → Prop := fun x₀ x₁ x₂ x₃ =>
      x₀ ∈ O ∧ x₁ ∈ O ∧ x₂ ∈ O ∧ x₃ ∈ O ∧ Γ.Adj x₀ x₁ ∧ Γ.Adj x₁ x₂ ∧ Γ.Adj x₂ x₃ ∧
        [x₀, x₁, x₂, x₃].Nodup
    (¬ ∃ x, hexagon x ∧ periodic x) →
      Nat.card (Γ.induce O).ConnectedComponent = 2 ∧
      (∀ Q, Nat.card (comp Q) = 16 ∧ ∃ φ : K ≃ comp Q,
        (∀ g i, (φ (g * s i) : {v : V // col v = false}) = r i (φ g)) ∧
          ∀ g h, T.Adj g h ↔ Γ.Adj (φ g) (φ h)) ∧
      ∃ σ : {v : V // col v = false} → {v : V // col v = false},
        (∀ x (hx : x ∈ O), ∃ hσ : σ x ∈ O,
          (Γ.induce O).connectedComponentMk ⟨σ x, hσ⟩ =
            (Γ.induce O).connectedComponentMk ⟨x, hx⟩ ∧
          ∀ y (hy : y ∈ O), (Γ.induce O).dist ⟨x, hx⟩ ⟨y, hy⟩ = 4 ↔ y = σ x) ∧
        (∀ x ∈ O, σ (σ x) = x) ∧
        (∀ x ∈ O, ∀ y ∈ O, Γ.Adj (σ x) (σ y) ↔ Γ.Adj x y) ∧
        (∀ x ∈ O, ∀ i, σ (r i x) = r i (σ x)) ∧
        (∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y → c (σ x) (σ y) = c x y) ∧
        (∀ Q (φ : K ≃ comp Q), (∀ g i, (φ (g * s i) : {v : V // col v = false}) = r i (φ g)) →
          ∀ g, σ (φ g) = φ (τ g)) ∧
        (∀ γ ∈ O, ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
          r i (r j (r i (r j γ))) = σ γ ∧ r k (r j (r k (r j γ))) = σ γ ∧
          c (r j γ) (r i (r j γ)) = i ∧ c (r j (r i (r j γ))) (σ γ) = i ∧
          c (r j γ) (r k (r j γ)) = k ∧ c (r j (r k (r j γ))) (σ γ) = k ∧
          r i (r j γ) ≠ r k (r j γ) ∧
          {m : {v : V // col v = false} × {v : V // col v = false} |
            path (r j γ) m.1 m.2 (σ γ)} =
            {(r i (r j γ), r j (r i (r j γ))), (r k (r j γ), r j (r k (r j γ)))}) ∧
        (∀ x ∈ O, ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
          r i (r k (r j x)) = r k (r j (r i x)) ∧ r j (r i (r k x)) = r k (r j (r i x)) ∧
          r i x ≠ r j x ∧ r j x ≠ r k x ∧ r i x ≠ r k x ∧
          {m : {v : V // col v = false} × {v : V // col v = false} |
            path x m.1 m.2 (r k (r j (r i x)))} =
            {(r i x, r j (r i x)), (r j x, r k (r j x)), (r k x, r i (r k x))} ∧
          r j (r k (r i x)) = r i (r j (r k x)) ∧ r k (r i (r j x)) = r i (r j (r k x)) ∧
          r i (r j (r k x)) ≠ r k (r j (r i x))) ∧
        ∀ x₀ x₁ x₂ x₃, path x₀ x₁ x₂ x₃ → ∃ a b d : Fin 3,
          x₁ = r a x₀ ∧ x₂ = r b x₁ ∧ x₃ = r d x₂ ∧ a ≠ b ∧ b ≠ d ∧
          ((a ≠ d ∧ {m : {v : V // col v = false} × {v : V // col v = false} |
              path x₀ m.1 m.2 x₃} =
              {(r a x₀, r b (r a x₀)), (r b x₀, r d (r b x₀)), (r d x₀, r a (r d x₀))}) ∨
            (a = d ∧ ∃ e, e ≠ a ∧ e ≠ b ∧ x₃ = σ (r b x₀) ∧
              {m : {v : V // col v = false} × {v : V // col v = false} |
                path x₀ m.1 m.2 x₃} =
                {(r a x₀, r b (r a x₀)), (r e x₀, r b (r e x₀))})) := by
  intro Γ O hexagon periodic comp path haper
  have F : IsFrame G col w ℓ p z q c ε := ⟨H, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩
  have haper' : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x :=
    fun x hx hpx => haper ⟨x, hx, hpx⟩
  refine ⟨card_components F hr haper', fun Q => ?_, sigmaMap G col w,
    fun x hx => sigmaMap_dist F hr haper' hx, fun x hx => sigmaMap_sigmaMap F hr haper' hx,
    fun x hx y hy => adj_sigmaMap_iff F hr haper' hx hy,
    fun x hx i => sigmaMap_r F hr haper' hx i,
    fun x hx y hy hxy => colour_sigmaMap F hr haper' hx hy hxy,
    fun Q φ hφ g => sigmaMap_equiv F hr φ hφ g, fun γ hγ i j k hij hjk hik => ?_,
    fun x hx i j k hij hjk hik => paths_cyclic_opp F hr haper' hx hij hjk hik,
    fun x₀ x₁ x₂ x₃ hpath => path_dichotomy F hr haper' hpath⟩
  ·
    obtain ⟨⟨φ, hφ⟩, hcard⟩ := exists_equiv F hr haper' Q
    exact ⟨hcard, φ, hφ, fun g h => (adj_iff_of_equiv F hr φ hφ g h).symm⟩
  ·
    obtain ⟨h1, h2, hne, hset⟩ := paths_to_sigmaMap F hr haper' hγ hij hjk hik
    have hδ := (hr j γ hγ).1
    refine ⟨h1, h2, (hr i _ hδ).2.2, ?_, (hr k _ hδ).2.2, ?_, hne, hset⟩
    · rw [← h1]
      exact (hr i _ (hr j _ (hr i _ hδ).1).1).2.2
    · rw [← h2]
      exact (hr k _ (hr j _ (hr k _ hδ).1).1).2.2

end CFSG.Combinatorics.AperiodicOppositeComponents

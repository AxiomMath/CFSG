module

public import CFSG.Combinatorics.HexagonAlternatingOctagonsOrbit
public import CFSG.Combinatorics.HexagonPeriodicPropagation

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.HexagonAlternatingOctagons

theorem exists_colour_moving {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (H : MooreHyp G) (col : G.Coloring Bool) (w : {v : V // col v = false})
    (ℓ : Fin 3 → V) (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    (p : Fin 3 → Fin 2 → {v : V // col v = false}) (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i))
    (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2)
    (hdata : IsFrameData G col w p z q c ε) :
    ∃ r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}, ∀ i x,
      (pointGraph G col).dist w x = 3 → ((pointGraph G col).dist w (r i x) = 3 ∧
        (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i) ∧
        ∀ y, (pointGraph G col).dist w y = 3 → (pointGraph G col).Adj x y → c x y = i →
          r i x = y := by
  have F : IsFrame G col w ℓ p z q c ε := ⟨H, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩
  have h : ∀ (i : Fin 3) (x : {v : V // col v = false}), ∃ y,
      (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w y = 3 ∧
        (pointGraph G col).Adj x y ∧ c x y = i := by
    intro i x
    by_cases hx : (pointGraph G col).dist w x = 3
    · obtain ⟨y, hy⟩ := F.exists_colour hx i
      exact ⟨y, fun _ => hy⟩
    · exact ⟨x, fun h => absurd h hx⟩
  choose r hr using h
  exact ⟨r, fun i x hx => ⟨hr i x hx, fun y hy hxy hc => F.r_eq hr hx hy hxy hc⟩⟩

theorem periodic_opposite_component_alternating_octagons_and_equal_third_points {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (H : MooreHyp G)
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
    ∀ Q : (Γ.induce O).ConnectedComponent,
      let QP : Set {v : V // col v = false} :=
        {x | ∃ h : x ∈ O, (Γ.induce O).connectedComponentMk ⟨x, h⟩ = Q}
      let hexagon : (Fin 6 → {v : V // col v = false}) → Prop := fun x =>
        Function.Injective x ∧ (∀ n, x n ∈ QP) ∧ ∀ n, Γ.Adj (x n) (x (n + 1))
      let periodic : (Fin 6 → {v : V // col v = false}) → Prop := fun x =>
        ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ ∀ n, c (x n) (x (n + 1)) = ![i, j, k, i, j, k] n
      (∃ x, hexagon x ∧ periodic x) →
      ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
        (∀ x₀ ∈ QP, ∀ x₁ ∈ QP, ∀ x₂ ∈ QP, ∀ x₃ ∈ QP, ∀ x₄ ∈ QP, ∀ x₅ ∈ QP, ∀ x₆ ∈ QP,
          Γ.Adj x₀ x₁ → Γ.Adj x₁ x₂ → Γ.Adj x₂ x₃ → Γ.Adj x₃ x₄ → Γ.Adj x₄ x₅ → Γ.Adj x₅ x₆ →
          c x₀ x₁ = k → c x₁ x₂ = i → c x₂ x₃ = j → c x₃ x₄ = i → c x₄ x₅ = j → c x₅ x₆ = k →
            [x₀, x₁, x₂, x₃, x₄, x₅, x₆].Nodup ∧
            (∀ m m' : V, G.Adj (x₀ : V) m → G.Adj (x₁ : V) m → G.Adj (x₅ : V) m' →
              G.Adj (x₆ : V) m' → m ≠ m') ∧
            Γ.dist w (z x₀ x₁) = 2 ∧ z x₀ x₁ = z x₅ x₆) ∧
        (∀ y : ℕ → {v : V // col v = false}, (∀ n ≤ 8, y n ∈ QP) →
          (∀ n < 8, Γ.Adj (y n) (y (n + 1))) →
          (∀ n < 8, c (y n) (y (n + 1)) = if Even n then i else j) →
            y 8 = y 0 ∧ ∀ a < 8, ∀ b < 8, y a = y b → a = b) ∧
        (∀ x ∈ QP, (r i ∘ r j)^[4] x = x) ∧
        (∀ x ∈ QP, ∃ y : Fin 8 → {v : V // col v = false}, Function.Injective y ∧ y 0 = x ∧
          (∀ n, Γ.Adj (y n) (y (n + 1)) ∧ c (y n) (y (n + 1)) = ![i, j, i, j, i, j, i, j] n) ∧
          {u | Relation.ReflTransGen (fun a b => b = r i a ∨ b = r j a) x u} = Set.range y) := by
  intro Γ O Q QP hexagon periodic hper i j k hij hjk hik
  have F : IsFrame G col w ℓ p z q c ε := ⟨H, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩
  have hSO : ∀ x ∈ QP, Γ.dist w x = 3 := fun x hx => hx.1
  have hSadj : ∀ x ∈ QP, ∀ y, Γ.dist w y = 3 → Γ.Adj x y → y ∈ QP := by
    rintro x ⟨hx, hxQ⟩ y hy hxy
    exact ⟨hy, (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := Γ.induce O) (v := ⟨x, hx⟩) (w := ⟨y, hy⟩) hxy).symm.trans hxQ⟩
  have hall : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → (∀ n, x n ∈ QP) →
      IsPeriodic c x := fun x hx hxQ =>
    (periodic_opposite_component_six_cycle_propagation G H col w ℓ hℓ hwℓ p hpℓ hpw hp z q c ε
      hdata Q hper).1 x ⟨hx.1, hxQ, hx.2.2⟩
  refine ⟨fun x₀ h₀ x₁ h₁ x₂ h₂ x₃ h₃ x₄ h₄ x₅ h₅ x₆ h₆ a01 a12 a23 a34 a45 a56 c01 c12 c23 c34
    c45 c56 => ?_, fun y hy hadj hcol => F.alternating_eight hr hSO hSadj hall hij hjk hik hy
      hadj hcol, fun x hx => F.pow_four hr hSO hSadj hall hij hjk hik hx,
    fun x hx => F.alternating_orbit hr hSO hSadj hall hij hjk hik hx⟩
  obtain ⟨n01, n02, n03, n04, n05, n06, n12, n13, n14, n15, n16, n23, n24, n25, n26, n34, n35,
    n36, n45, n46, n56⟩ := F.seven_ne hij hjk hik (hSO _ h₀) (hSO _ h₁) (hSO _ h₂) (hSO _ h₃)
      (hSO _ h₄) (hSO _ h₅) (hSO _ h₆) a01 a12 a23 a34 a45 a56 c01 c12 c23 c34 c45 c56
  have hd := point_dist_eq_iff H.conn col
  have hV : ∀ {a b : {v : V // col v = false}}, a ≠ b → (a : V) ≠ b :=
    fun h h' => h (Subtype.ext h')
  refine ⟨nodup_seven n01 n02 n03 n04 n05 n06 n12 n13 n14 n15 n16 n23 n24 n25 n26 n34 n35 n36
    n45 n46 n56, fun m m' h0m h1m h5m _ hmm => ?_, ?_,
    F.seven_third hSO hSadj hall hij hjk hik h₀ h₁ h₂ h₃ h₄ h₅ h₆ a01 a12 a23 a34 a45 a56 c01
      c12 c23 c34 c45 c56⟩
  ·
    subst hmm
    exact not_three_far_on_line H col ((hd w _ 3).mp (hSO _ h₀)) ((hd w _ 3).mp (hSO _ h₁))
      ((hd w _ 3).mp (hSO _ h₅)) h0m h1m h5m (hV n01) (hV n05) (hV n15)
  ·
    obtain ⟨_m, -, -, -, -, hz4, -⟩ := F.edge (hSO _ h₀) (hSO _ h₁) a01
    exact (hd w _ 2).mpr hz4

end CFSG.Combinatorics.HexagonAlternatingOctagons

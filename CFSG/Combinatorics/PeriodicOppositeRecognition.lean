module

public import CFSG.Combinatorics.PeriodicOppositeRecognitionSupport
public import CFSG.Combinatorics.HexagonAlternatingOctagons
public import CFSG.Combinatorics.HexagonStabilizerFaithful

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.HexagonPeriodicPropagation
  CFSG.Combinatorics.HexagonAlternatingOctagons CFSG.Combinatorics.AperiodicOppositeComponents
  CFSG.Combinatorics.HexagonStabilizerFaithful
open CFSG.Combinatorics.FourByFourPeriodicGraph (Vertex o P4 IsColouredIso
  four_by_four_periodic_cubic_graph_local_cycles_and_automorphism_bound)

namespace CFSG.Combinatorics.PeriodicOppositeRecognition

theorem periodic_point_opposite_graph_recognition_and_automorphism_bound {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (H : MooreHyp G)
    (col : G.Coloring Bool) (w : {v : V // col v = false}) (ℓ : Fin 3 → V)
    (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    (p : Fin 3 → Fin 2 → {v : V // col v = false}) (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i))
    (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2)
    (hdata : IsFrameData G col w p z q c ε) :
    let Γ : SimpleGraph {v : V // col v = false} := pointGraph G col
    let O : Set {v : V // col v = false} := {x | Γ.dist w x = 3}
    let hexagon : (Fin 6 → {v : V // col v = false}) → Prop := fun x =>
      Function.Injective x ∧ (∀ n, x n ∈ O) ∧ ∀ n, Γ.Adj (x n) (x (n + 1))
    let periodic : (Fin 6 → {v : V // col v = false}) → Prop := fun x =>
      ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ ∀ n, c (x n) (x (n + 1)) = ![i, j, k, i, j, k] n
    let colour : Fin 3 → O → O → Prop := fun i a b => (Γ.induce O).Adj a b ∧ c a b = i
    (∃ x, hexagon x ∧ periodic x) →
      (Γ.induce O).Connected ∧
      (∀ x (hx : x ∈ O), ∃! φ : Vertex ≃ O, φ o = ⟨x, hx⟩ ∧ IsColouredIso colour φ) ∧
      (∀ φ : Vertex ≃ O, IsColouredIso colour φ →
        ∀ u v, P4.Adj u v ↔ (Γ.induce O).Adj (φ u) (φ v)) ∧
      (∀ f : G ≃g G, f ∈ partAut G col ↔
        f '' {v | col v = false} = {v | col v = false} ∧
          f '' {v | col v = true} = {v | col v = true}) ∧
      Nat.card (MulAction.stabilizer (partAut G col) (w : V)) ≤ 192 ∧
      Nat.card (partAut G col) ≤ 12096 := by
  intro Γ O hexagon periodic colour hper
  have F : IsFrame G col w ℓ p z q c ε := ⟨H, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩
  obtain ⟨r, hr'⟩ := exists_colour_moving G H col w ℓ hℓ hwℓ p hpℓ hpw hp z q c ε hdata
  have hr : ∀ i x, Γ.dist w x = 3 → Γ.dist w (r i x) = 3 ∧ Γ.Adj x (r i x) ∧ c x (r i x) = i :=
    fun i x hx => (hr' i x hx).1
  obtain ⟨x₀, ⟨hx₀i, hx₀O, hx₀a⟩, hx₀p⟩ := hper
  set Q := (oppGraph G col w).connectedComponentMk ⟨x₀ 0, hx₀O 0⟩
  have hx₀Q : ∀ n, x₀ n ∈ compSet Q := by
    have h0 : x₀ 0 ∈ compSet Q := ⟨hx₀O 0, rfl⟩
    have h1 := mem_compSet_of_adj h0 (hx₀O 1) (hx₀a 0)
    have h2 := mem_compSet_of_adj h1 (hx₀O 2) (hx₀a 1)
    have h3 := mem_compSet_of_adj h2 (hx₀O 3) (hx₀a 2)
    have h4 := mem_compSet_of_adj h3 (hx₀O 4) (hx₀a 3)
    have h5 := mem_compSet_of_adj h4 (hx₀O 5) (hx₀a 4)
    intro n
    fin_cases n
    exacts [h0, h1, h2, h3, h4, h5]
  have hperQ : ∃ x : Fin 6 → {v : V // col v = false},
      (Function.Injective x ∧ (∀ n, x n ∈ compSet Q) ∧ ∀ n, Γ.Adj (x n) (x (n + 1))) ∧
        periodic x :=
    ⟨x₀, ⟨hx₀i, hx₀Q, hx₀a⟩, hx₀p⟩
  have hall : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x →
      (∀ n, x n ∈ compSet Q) → IsPeriodic c x := fun x hx hxQ =>
    (periodic_opposite_component_six_cycle_propagation G H col w ℓ hℓ hwℓ p hpℓ hpw hp z q c ε
      hdata Q hperQ).1 x ⟨hx.1, hxQ, hx.2.2⟩
  have hpow : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x ∈ compSet Q,
      (r i ∘ r j)^[4] x = x := fun i j k hij hjk hik =>
    (periodic_opposite_component_alternating_octagons_and_equal_third_points G H col w ℓ hℓ hwℓ
      p hpℓ hpw hp z q c ε hdata r hr Q hperQ i j k hij hjk hik).2.2.1
  obtain ⟨hrec, hcard⟩ := component_recognition F hr Q hall hpow
  obtain ⟨hO32, hP63⟩ := ncard_oppSet_and_card_points F
  have hQO : compSet Q = oppSet G col w := Set.eq_of_subset_of_ncard_le (fun x hx => hx.1)
    (by rw [hO32, ← Nat.card_coe_set_eq, hcard]) (Set.toFinite _)
  have hmemQ : ∀ x : oppSet G col w, (oppGraph G col w).connectedComponentMk x = Q := by
    intro x
    have hx : (x : {v : V // col v = false}) ∈ compSet Q := by
      rw [hQO]
      exact x.2
    exact hx.2
  have hconn : (oppGraph G col w).Connected := by
    have : Nonempty (oppSet G col w) := ⟨⟨x₀ 0, hx₀O 0⟩⟩
    exact ⟨fun a b => SimpleGraph.ConnectedComponent.exact ((hmemQ a).trans (hmemQ b).symm)⟩
  let e : compSet Q ≃ oppSet G col w := Equiv.subtypeEquivRight fun x => by rw [hQO]
  have hiso : ∀ x (hx : x ∈ O), ∃! φ : Vertex ≃ O, φ o = ⟨x, hx⟩ ∧ IsColouredIso colour φ := by
    intro x hx
    obtain ⟨φ₀, ⟨hφ₀o, hφ₀⟩, huniq⟩ := hrec (e.symm ⟨x, hx⟩)
    have h₀ : ((φ₀ o : compSet Q) : {v : V // col v = false}) = x := congrArg Subtype.val hφ₀o
    refine ⟨φ₀.trans e, ⟨Subtype.ext h₀, (isColouredIso_iff F hr (φ₀.trans e)).mpr hφ₀⟩, ?_⟩
    rintro ψ ⟨hψo, hψ⟩
    have hψ' := (isColouredIso_iff F hr ψ).mp hψ
    have h₁ : ((ψ o : O) : {v : V // col v = false}) = x := congrArg Subtype.val hψo
    have h := huniq (ψ.trans e.symm) ⟨Subtype.ext h₁, hψ'⟩
    exact Equiv.ext fun u => Subtype.ext (congrArg (fun χ => (χ u : {v : V // col v = false})) h)
  have hadj : ∀ φ : Vertex ≃ O, IsColouredIso colour φ →
      ∀ u v, P4.Adj u v ↔ (Γ.induce O).Adj (φ u) (φ v) := fun φ hφ =>
    adj_iff_of_isColouredIso φ hφ
  obtain ⟨φ, ⟨-, hφ⟩, -⟩ := hiso (x₀ 0) (hx₀O 0)
  let iso : P4 ≃g Γ.induce O := ⟨φ, fun {u v} => (hadj φ hφ u v).symm⟩
  have hAw : Nat.card (MulAction.stabilizer (partAut G col) (w : V)) ≤ 192 :=
    ((hexagon_point_stabilizer_opposite_layer_action_is_faithful G H.card H.conn H.deg col
      H.cyc w).2.2.2 P4 ⟨iso.symm⟩).trans
        four_by_four_periodic_cubic_graph_local_cycles_and_automorphism_bound.2.2.2.2.2.2.2.2.2.2.2
  have horb : Nat.card (partAut G col ⧸ MulAction.stabilizer (partAut G col) (w : V)) ≤ 63 := by
    rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (partAut G col) (w : V)),
      ← hP63, ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) fun y y' h =>
      Subtype.ext (congrArg (fun t : {v : V // col v = false} => (t : V)) h)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp y.2
    rw [← hg]
    exact (mem_partAut.mp g.2 w).trans w.2
  refine ⟨hconn, hiso, hadj, mem_partAut_iff_image, hAw, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MulAction.stabilizer (partAut G col) (w : V))]
  calc _ ≤ 63 * 192 := Nat.mul_le_mul horb hAw
    _ = 12096 := by norm_num

end CFSG.Combinatorics.PeriodicOppositeRecognition

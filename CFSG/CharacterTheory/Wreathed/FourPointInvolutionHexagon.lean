module

public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagonSupport
public import CFSG.CharacterTheory.Wreathed.FourPointConnectedGraph

public noncomputable section

namespace CFSG.Wreathed.FourPointInvolutionHexagon

open Equiv CFSG.Assembly CFSG.GroupTheory.SevenInvolutionWreathLaw
  CFSG.GroupTheory.InvolutionHexagon

open scoped Classical

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_involution_generalized_hexagon_and_regular_opposite_action
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let P := {g : G // orderOf g = 2}
    let L := {T : Set G // ∃ u v : G, orderOf u = 2 ∧ orderOf v = 2 ∧ u ≠ v ∧ u * v = v * u ∧
      T = {u, v, u * v}}
    let Δ : SimpleGraph (P ⊕ L) :=
      SimpleGraph.fromRel fun a b => ∃ p T, a = Sum.inl p ∧ b = Sum.inr T ∧ (p : G) ∈ T.1
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    Nat.card P = 63 ∧ Nat.card L = 63 ∧
    (∀ p : P, {T : L | (p : G) ∈ T.1}.ncard = 3) ∧
    (∀ T : L, {p : P | (p : G) ∈ T.1}.ncard = 3) ∧
    Δ.Connected ∧ Δ.girth = 12 ∧ Δ.diam = 6 ∧
    involutionGraph G =
      SimpleGraph.fromRel (fun p q : P => ∃ T : L, (p : G) ∈ T.1 ∧ (q : G) ∈ T.1) ∧
    (∀ (p : P) (k : Fin 4),
      {q : P | (involutionGraph G).dist p q = k}.ncard = ![1, 6, 24, 32] k) ∧
    (∀ (p : P) (T : L), ∃! q : P, (q : G) ∈ T.1 ∧
      ∀ q' : P, (q' : G) ∈ T.1 → (involutionGraph G).dist p q ≤ (involutionGraph G).dist p q') ∧
    (∃ ρ : G →* (Δ ≃g Δ), Function.Injective ρ ∧
      (∀ (g : G) (p : P), ∃ p' : P, ρ g (Sum.inl p) = Sum.inl p' ∧ (p' : G) = g * p * g⁻¹) ∧
      (∀ (g : G) (T : L), ∃ T' : L, ρ g (Sum.inr T) = Sum.inr T' ∧
        T'.1 = (fun y => g * y * g⁻¹) '' T.1)) ∧
    Nat.card (S : Subgroup G) = 32 ∧ (∀ g ∈ (S : Subgroup G), g * x = x * g) ∧
    ∃ x' : P, (x' : G) = x ∧ {z : P | (involutionGraph G).dist x' z = 3}.ncard = 32 ∧
      ∀ z z' : P, (involutionGraph G).dist x' z = 3 → (involutionGraph G).dist x' z' = 3 →
        ∃! s : (S : Subgroup G), (s : G) * z * (s : G)⁻¹ = z' := by
  intro P L Δ x
  obtain ⟨hn2, -, -, -, -, hcard, hval, -⟩ :=
    FourPointConnectedGraph.four_point_connected_involution_graph_and_trivial_original_odd_core
      hnonab n hn S e alpha
  subst hn2
  have hconj := all_involutions_conjugate_of_simple_wreathed hnonab 2 hn S e
  have : Finite (Wreath (2 ^ 2)) := Nat.finite_of_card_ne_zero (by rw [card_wreath]; norm_num)
  obtain ⟨hlaw, -⟩ := localData hconj S e hval
  obtain ⟨hL, -, hpts, hconn, hgirth, hdiam, hΓ, -, -, hlayer, hnear, hρp, hρT, hfaith, hreg⟩ :=
    involution_hexagon_of_local_data hcard hlaw hval
  have H := involutionHexagonData hcard hlaw hval
  have hx2 : orderOf x = 2 := by
    rw [orderOf_injective _ (wreathModelHom_injective S e)]
    exact (wreath_center_involution_and_quaternion_coordinates 2 le_rfl).involution_orders.1
  have hSx : ∀ g ∈ (S : Subgroup G), g * x = x * g := fun g hg => commute_x_of_mem S e hg
  obtain ⟨h32, hregx⟩ := hreg ⟨x, hx2⟩ S (card_sylow S e) hSx
  exact ⟨hcard, hL, hpts, H.ncard_points, hconn, hgirth, hdiam, hΓ, hlayer, hnear,
    ⟨conjAction G, hfaith inferInstance, hρp, hρT⟩, card_sylow S e, hSx, ⟨x, hx2⟩, rfl, h32,
    hregx⟩

end CFSG.Wreathed.FourPointInvolutionHexagon

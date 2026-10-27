module

public import CFSG.Combinatorics.PeriodicHexagonIsomorphism
public import CFSG.Combinatorics.AperiodicDualPeriodic

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.HexagonPeriodicPropagation
  CFSG.Combinatorics.HexagonAlternatingOctagons CFSG.Combinatorics.AperiodicOppositeComponents
  CFSG.Combinatorics.OuterLayer

namespace CFSG.Combinatorics.HexagonUniqueDuality

universe u u'

section OneGraph

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem exists_point (H : MooreHyp G) (col : G.Coloring Bool) : ∃ w : V, col w = false := by
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by rw [H.card]; norm_num)
  cases hv : col v with
  | false => exact ⟨v, hv⟩
  | true =>
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset v).card by
      rw [SimpleGraph.card_neighborFinset_eq_degree, H.deg]
      norm_num)
    exact ⟨u, col_eq_false_of_adj col hv ((SimpleGraph.mem_neighborFinset _ _ _).mp hu).symm⟩

theorem exists_periodic_frame (H : MooreHyp G) (col : G.Coloring Bool) :
    ∃ (e : Bool) (col' : G.Coloring Bool), (∀ v, col' v = xor (col v) e) ∧
      ∃ (w : {v : V // col' v = false}) (ℓ : Fin 3 → V)
        (p : Fin 3 → Fin 2 → {v : V // col' v = false})
        (z q : {v : V // col' v = false} → {v : V // col' v = false} → {v : V // col' v = false})
        (c : {v : V // col' v = false} → {v : V // col' v = false} → Fin 3)
        (ε : {v : V // col' v = false} → {v : V // col' v = false} → Fin 2),
        Function.Injective ℓ ∧ (∀ i, G.Adj (w : V) (ℓ i)) ∧ (∀ i e, G.Adj (p i e : V) (ℓ i)) ∧
          (∀ i e, p i e ≠ w) ∧ (∀ i, Function.Injective (p i)) ∧
          IsFrameData G col' w p z q c ε ∧ ∃ x, IsHex G col' w x ∧ IsPeriodic c x := by
  obtain ⟨w₀, hw₀⟩ := exists_point H col
  obtain ⟨ℓ, p, z, q, c, ε, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩ := exists_frameData H col ⟨w₀, hw₀⟩
  by_cases hper : ∃ x, IsHex G col ⟨w₀, hw₀⟩ x ∧ IsPeriodic c x
  · exact ⟨false, col, fun v => (Bool.xor_false (col v)).symm, ⟨w₀, hw₀⟩, ℓ, p, z, q, c, ε, hℓ,
      hwℓ, hpℓ, hpw, hp, hdata, hper⟩
  obtain ⟨r, hr'⟩ := exists_colour_moving G H col ⟨w₀, hw₀⟩ ℓ hℓ hwℓ p hpℓ hpw hp z q c ε hdata
  have hr : ∀ i x, (pointGraph G col).dist ⟨w₀, hw₀⟩ x = 3 →
      (pointGraph G col).dist ⟨w₀, hw₀⟩ (r i x) = 3 ∧ (pointGraph G col).Adj x (r i x) ∧
        c x (r i x) = i := fun i x hx => (hr' i x hx).1
  have hu : dualCol col (ℓ 0) = false := by
    rw [dualCol_apply, col_eq_true_of_adj col hw₀ (hwℓ 0)]
    rfl
  obtain ⟨⟨ℓ', p', z', q', c', ε', hℓ', hwℓ', hpℓ', hpw', hp', hdata'⟩, hall⟩ :=
    lines_through_an_aperiodic_point_are_dual_periodic G H col ⟨w₀, hw₀⟩ ℓ hℓ hwℓ p hpℓ hpw hp z
      q c ε hdata r hr hper ⟨ℓ 0, hu⟩ (hwℓ 0)
  exact ⟨true, dualCol col, fun v => by simp, ⟨ℓ 0, hu⟩, ℓ', p', z', q', c', ε', hℓ', hwℓ', hpℓ',
    hpw', hp', hdata', hall ℓ' hℓ' hwℓ' p' hpℓ' hpw' hp' z' q' c' ε' hdata'⟩

end OneGraph

theorem order_two_generalized_hexagons_unique_up_to_duality {V : Type u} {V' : Type u'}
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 126)
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 3) (col : G.Coloring Bool)
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    [Fintype V'] (G' : SimpleGraph V') [DecidableRel G'.Adj] (hcard' : Fintype.card V' = 126)
    (hconn' : G'.Connected) (hdeg' : ∀ v, G'.degree v = 3) (col' : G'.Coloring Bool)
    (hcyc' : ∀ (v : V') (c : G'.Walk v v), c.IsCycle → 12 ≤ c.length) :
    ∃ (ε₁ ε₂ : Bool) (f : G ≃g G'), f '' {v | col v = ε₁} = {v | col' v = ε₂} ∧
      f '' {v | col v = !ε₁} = {v | col' v = !ε₂} := by
  classical
  have H : MooreHyp G := ⟨hcard, hconn, hdeg, hcyc⟩
  have H' : MooreHyp G' := ⟨hcard', hconn', hdeg', hcyc'⟩
  obtain ⟨e₁, col₁, hcol₁, w₁, ℓ₁, p₁, z₁, q₁, c₁, η₁, a1, a2, a3, a4, a5, a6, hper₁⟩ :=
    exists_periodic_frame H col
  obtain ⟨e₂, col₂, hcol₂, w₂, ℓ₂, p₂, z₂, q₂, c₂, η₂, b1, b2, b3, b4, b5, b6, hper₂⟩ :=
    exists_periodic_frame H' col'
  obtain ⟨⟨f, hf, -⟩, -⟩ := periodic_point_hexagons_are_isomorphic G H col₁ w₁ ℓ₁ a1 a2 p₁ a3 a4
    a5 z₁ q₁ c₁ η₁ a6 G' H' col₂ w₂ ℓ₂ b1 b2 p₂ b3 b4 b5 z₂ q₂ c₂ η₂ b6 hper₁ hper₂
  have hbool : ∀ a b e e' : Bool, xor a e' = xor b e →
      (a = e' ↔ b = e) ∧ (a = !e' ↔ b = !e) := by decide
  have key : ∀ v, (col' (f v) = e₂ ↔ col v = e₁) ∧ (col' (f v) = !e₂ ↔ col v = !e₁) :=
    fun v => hbool _ _ _ _ (by rw [← hcol₂, ← hcol₁]; exact hf v)
  have himage : ∀ {S : Set V} {T : Set V'}, (∀ v, f v ∈ T ↔ v ∈ S) → f '' S = T := by
    intro S T h
    ext v'
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (h v).mpr hv
    · intro hv'
      refine ⟨f.symm v', (h _).mp ?_, f.apply_symm_apply v'⟩
      rwa [f.apply_symm_apply]
  exact ⟨e₁, e₂, f, himage fun v => (key v).1, himage fun v => (key v).2⟩

end CFSG.Combinatorics.HexagonUniqueDuality

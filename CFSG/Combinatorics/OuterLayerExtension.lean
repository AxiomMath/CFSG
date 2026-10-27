module

public import CFSG.Combinatorics.OuterLayerExtensionStep

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers

namespace CFSG.Combinatorics.OuterLayer

universe u u'

section TwoFrames

variable {V : Type u} {V' : Type u'} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [Fintype V'] [DecidableEq V'] {G' : SimpleGraph V'} [DecidableRel G'.Adj]
  {col : G.Coloring Bool} {col' : G'.Coloring Bool} {w : {v : V // col v = false}}
  {w' : {v : V' // col' v = false}}

omit [DecidableEq V] [DecidableEq V'] in
theorem dist_map_point (H : MooreHyp G) (H' : MooreHyp G') {f : G ≃g G'}
    (hf : ∀ v, col' (f v) = col v) (hfw : f (w : V) = (w' : V')) (x : {v : V // col v = false}) :
    (pointGraph G' col').dist w' ⟨f x, (hf x).trans x.2⟩ = (pointGraph G col).dist w x := by
  apply (point_dist_eq_iff H'.conn col' w' ⟨f x, (hf x).trans x.2⟩ _).mpr
  change G'.dist (w' : V') (f x) = 2 * (pointGraph G col).dist w x
  rw [← hfw, dist_iso f, dist_eq_two_mul H w x]

theorem eq_of_agree (H : MooreHyp G) (H' : MooreHyp G') {i : ℕ} (hi : i = 1 ∨ i = 2)
    {f g : G ≃g G'} (hf : ∀ v, col' (f v) = col v) (hg : ∀ v, col' (g v) = col v)
    (hfw : f (w : V) = (w' : V')) (hgw : g (w : V) = (w' : V'))
    (hfg : ∀ x : {v : V // col v = false}, i ≤ (pointGraph G col).dist w x → f x = g x) :
    f = g := by
  have hpts : ∀ x : {v : V // col v = false}, f x = g x := by
    intro x
    by_cases hx : i ≤ (pointGraph G col).dist w x
    · exact hfg x hx
    by_cases hx0 : (pointGraph G col).dist w x = 0
    · have hwx : (w : V) = x :=
        H.conn.dist_eq_zero_iff.mp (by rw [dist_eq_two_mul H w x, hx0])
      rw [← hwx, hfw, hgw]
    have hx1 : (pointGraph G col).dist w x = i - 1 := by omega
    obtain ⟨y, -, hy, hyx, -⟩ := exists_outward_point H hi hx1 (x : V)
    have hfy : f y = g y := hfg y hy.ge
    have hyx2 : G.dist (y : V) x = 2 := (point_adj_iff H.conn col y x).mp hyx
    have hfy' : (pointGraph G' col').dist w' ⟨f y, (hf y).trans y.2⟩ = i :=
      (dist_map_point H H' hf hfw y).trans hy
    have hadjf : (pointGraph G' col').Adj ⟨f y, (hf y).trans y.2⟩ ⟨f x, (hf x).trans x.2⟩ :=
      (point_adj_iff H'.conn col' _ _).mpr (by
        change G'.dist (f y) (f x) = 2
        rw [dist_iso f]
        exact hyx2)
    have hadjg : (pointGraph G' col').Adj ⟨f y, (hf y).trans y.2⟩ ⟨g x, (hg x).trans x.2⟩ :=
      (point_adj_iff H'.conn col' _ _).mpr (by
        change G'.dist (f y) (g x) = 2
        rw [hfy, dist_iso g]
        exact hyx2)
    have := (existsUnique_pred H' hi hfy').unique
      ⟨(dist_map_point H H' hf hfw x).trans hx1, hadjf⟩
      ⟨(dist_map_point H H' hg hgw x).trans hx1, hadjg⟩
    exact congrArg Subtype.val this
  refine RelIso.ext fun v => ?_
  cases hv : col v with
  | false => exact hpts ⟨v, hv⟩
  | true =>
    obtain ⟨a, b, c, hab, -, -, hN⟩ := Finset.card_eq_three.mp
      (show (G.neighborFinset v).card = 3 by
        rw [SimpleGraph.card_neighborFinset_eq_degree, H.deg])
    have av : G.Adj a v := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
    have bv : G.Adj b v := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
    have ha : col a = false := col_eq_false_of_adj col hv av
    have hb : col b = false := col_eq_false_of_adj col hv bv
    have ga : G'.Adj (f a) (g v) := by
      rw [show f a = g a from hpts ⟨a, ha⟩]
      exact g.map_adj_iff.mpr av
    have gb : G'.Adj (f b) (g v) := by
      rw [show f b = g b from hpts ⟨b, hb⟩]
      exact g.map_adj_iff.mpr bv
    exact eq_of_adj_adj H' col' (fun e => hab (f.injective e))
      ((hf a).trans (ha.trans (hb.symm.trans (hf b).symm))) (f.map_adj_iff.mpr av)
      (f.map_adj_iff.mpr bv) ga gb

end TwoFrames

theorem layer_preserving_outer_isomorphism_extends_uniquely {V : Type u} {V' : Type u'}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 126) (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 3)
    (col : G.Coloring Bool) (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (w : {v : V // col v = false})
    [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj]
    (hcard' : Fintype.card V' = 126) (hconn' : G'.Connected) (hdeg' : ∀ v, G'.degree v = 3)
    (col' : G'.Coloring Bool) (hcyc' : ∀ (v : V') (c : G'.Walk v v), c.IsCycle → 12 ≤ c.length)
    (w' : {v : V' // col' v = false})
    (i : ℕ) (hi : i = 1 ∨ i = 2) (ψ : (outerSystem G col w i).Iso (outerSystem G' col' w' i)) :
    (∃! f : G ≃g G', (∀ v, col' (f v) = col v) ∧ f (w : V) = (w' : V') ∧
      (∀ x : (outerSystem G col w i).Pt, f x.1.1 = (ψ.pts x).1.1) ∧
      ∀ m : (outerSystem G col w i).Ln, f m.1 = (ψ.lines m).1) ∧
    ∀ f : G ≃g G', (∀ v, col' (f v) = col v) → f (w : V) = (w' : V') →
      (∀ x : (outerSystem G col w i).Pt, f x.1.1 = (ψ.pts x).1.1) →
      (∀ m : (outerSystem G col w i).Ln, f m.1 = (ψ.lines m).1) →
      ∀ (r : ℕ) (v : V), (∃ x : {v : V // col v = false}, (x : V) = v ∧
        (pointGraph G col).dist w x = r) ↔
        ∃ x' : {v : V' // col' v = false}, (x' : V') = f v ∧
          (pointGraph G' col').dist w' x' = r := by
  have H : MooreHyp G := ⟨hcard, hconn, hdeg, hcyc⟩
  have H' : MooreHyp G' := ⟨hcard', hconn', hdeg', hcyc'⟩
  obtain ⟨χ₀, hχp, hχl⟩ : ∃ χ₀ : (outerSystem G col w 0).Iso (outerSystem G' col' w' 0),
      (∀ (x : (outerSystem G col w 0).Pt) (hx : i ≤ (pointGraph G col).dist w x.1),
        (χ₀.pts x).1 = (ψ.pts ⟨x.1, hx⟩).1) ∧
      ∀ (m : (outerSystem G col w 0).Ln) (hm : IsOuterLine G col w i m.1),
        (χ₀.lines m).1 = (ψ.lines ⟨m.1, hm⟩).1 := by
    rcases hi with rfl | rfl
    · exact exists_iso_pred H H' (Or.inl rfl) ψ
    · obtain ⟨χ₁, h1p, h1l⟩ := exists_iso_pred H H' (Or.inr rfl) ψ
      obtain ⟨χ₀, h0p, h0l⟩ := exists_iso_pred H H' (Or.inl rfl) χ₁
      refine ⟨χ₀, fun x hx => ?_, fun m hm => ?_⟩
      · rw [h0p x (by omega)]
        exact h1p ⟨x.1, by omega⟩ hx
      · rw [h0l m (hm.mono (by norm_num))]
        exact h1l ⟨m.1, hm.mono (by norm_num)⟩ hm
  obtain ⟨f, hfcol, hfp, hfl⟩ := exists_graphIso χ₀
  have hfw : f (w : V) = (w' : V') := by
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : (outerSystem G col w 0).Pt, x₀.1 = w := ⟨⟨w, Nat.zero_le _⟩, rfl⟩
    have hmk : (pointGraph G' col').dist w' (χ₀.pts x₀).1 = 0 :=
      (χ₀.marked_iff x₀).mp (by
        change (pointGraph G col).dist w x₀.1 = 0
        rw [hx₀]
        exact SimpleGraph.dist_self)
    have h0 : (w' : V') = (χ₀.pts x₀).1.1 :=
      H'.conn.dist_eq_zero_iff.mp (by rw [dist_eq_two_mul H' w' _, hmk])
    rw [← hx₀, hfp x₀, ← h0]
  have hfp' : ∀ x : (outerSystem G col w i).Pt, f x.1.1 = (ψ.pts x).1.1 := by
    intro x
    have h1 := hfp ⟨x.1, Nat.zero_le _⟩
    have h2 := congrArg Subtype.val (hχp ⟨x.1, Nat.zero_le _⟩ x.2)
    exact h1.trans h2
  have hfl' : ∀ m : (outerSystem G col w i).Ln, f m.1 = (ψ.lines m).1 := by
    intro m
    have h1 := hfl ⟨m.1, m.2.mono (Nat.zero_le i)⟩
    have h2 := hχl ⟨m.1, m.2.mono (Nat.zero_le i)⟩ m.2
    exact h1.trans h2
  refine ⟨⟨f, ⟨hfcol, hfw, hfp', hfl'⟩, fun g ⟨hg, hgw, hgp, _⟩ =>
    eq_of_agree H H' hi hg hfcol hgw hfw fun x hx =>
      (hgp ⟨x, hx⟩).trans (hfp' ⟨x, hx⟩).symm⟩, ?_⟩
  intro g hg hgw _ _ r v
  constructor
  · rintro ⟨x, rfl, hx⟩
    exact ⟨⟨g x, (hg x).trans x.2⟩, rfl, (dist_map_point H H' hg hgw x).trans hx⟩
  · rintro ⟨x', hx', hr⟩
    have hv : col v = false := by
      rw [← hg v, ← hx']
      exact x'.2
    have hx'' : (⟨g v, (hg v).trans hv⟩ : {v : V' // col' v = false}) = x' := Subtype.ext hx'.symm
    rw [← hx''] at hr
    exact ⟨⟨v, hv⟩, rfl, (dist_map_point H H' hg hgw ⟨v, hv⟩).symm.trans hr⟩

end CFSG.Combinatorics.OuterLayer

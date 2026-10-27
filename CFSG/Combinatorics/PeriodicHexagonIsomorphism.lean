module

public import CFSG.Combinatorics.PeriodicHexagonIsomorphismMap
public import CFSG.Combinatorics.OuterLayerExtension

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.HexagonPeriodicPropagation
  CFSG.Combinatorics.AperiodicOppositeComponents CFSG.Combinatorics.PeriodicOppositeRecognition

namespace CFSG.Combinatorics.OuterLayer

universe u u'

theorem periodic_point_hexagons_are_isomorphic {V : Type u} {V' : Type u'}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (H : MooreHyp G)
    (col : G.Coloring Bool) (w : {v : V // col v = false}) (ℓ : Fin 3 → V)
    (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    (p : Fin 3 → Fin 2 → {v : V // col v = false}) (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i))
    (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2)
    (hdata : IsFrameData G col w p z q c ε)
    [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj] (H' : MooreHyp G')
    (col' : G'.Coloring Bool) (w' : {v : V' // col' v = false}) (ℓ' : Fin 3 → V')
    (hℓ' : Function.Injective ℓ') (hwℓ' : ∀ i, G'.Adj (w' : V') (ℓ' i))
    (p' : Fin 3 → Fin 2 → {v : V' // col' v = false}) (hpℓ' : ∀ i e, G'.Adj (p' i e : V') (ℓ' i))
    (hpw' : ∀ i e, p' i e ≠ w') (hp' : ∀ i, Function.Injective (p' i))
    (z' q' : {v : V' // col' v = false} → {v : V' // col' v = false} → {v : V' // col' v = false})
    (c' : {v : V' // col' v = false} → {v : V' // col' v = false} → Fin 3)
    (ε' : {v : V' // col' v = false} → {v : V' // col' v = false} → Fin 2)
    (hdata' : IsFrameData G' col' w' p' z' q' c' ε')
    (hper : ∃ x, IsHex G col w x ∧ IsPeriodic c x)
    (hper' : ∃ x, IsHex G' col' w' x ∧ IsPeriodic c' x) :
    (∃ f : G ≃g G', (∀ v, col' (f v) = col v) ∧ f (w : V) = (w' : V')) ∧
    ∀ φ : oppGraph G col w ≃g oppGraph G' col' w',
      (∀ a b, (oppGraph G col w).Adj a b → c' (φ a) (φ b) = c a b) →
      ∃! f : G ≃g G', (∀ v, col' (f v) = col v) ∧ f (w : V) = (w' : V') ∧
        ∀ x : oppSet G col w,
          f ((x : {v : V // col v = false}) : V) = ((φ x : {v : V' // col' v = false}) : V') := by
  have F : IsFrame G col w ℓ p z q c ε := ⟨H, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩
  have F' : IsFrame G' col' w' ℓ' p' z' q' c' ε' := ⟨H', hℓ', hwℓ', hpℓ', hpw', hp', hdata'⟩
  have hle : ∀ x : {v : V // col v = false}, (pointGraph G col).dist w x ≤ 3 := fun x => by
    rw [(point_dist H.conn col w x).1]
    have := dist_le_six H.cyc H.conn col H.deg H.card (w : V) x
    omega
  have hb : ∀ φ : oppGraph G col w ≃g oppGraph G' col' w',
      (∀ a b, (oppGraph G col w).Adj a b → c' (φ a) (φ b) = c a b) →
      ∃! f : G ≃g G', (∀ v, col' (f v) = col v) ∧ f (w : V) = (w' : V') ∧
        ∀ x : oppSet G col w,
          f ((x : {v : V // col v = false}) : V) = ((φ x : {v : V' // col' v = false}) : V') := by
    intro φ hφ
    obtain ⟨χ, hχ⟩ := exists_outer_iso F F' hper hper' φ hφ
    obtain ⟨⟨f, ⟨hfcol, hfw, hfp, -⟩, -⟩, -⟩ := layer_preserving_outer_isomorphism_extends_uniquely
      G H.card H.conn H.deg col H.cyc w G' H'.card H'.conn H'.deg col' H'.cyc w' 2 (Or.inr rfl) χ
    have hfO : ∀ x : oppSet G col w,
        f ((x : {v : V // col v = false}) : V) = ((φ x : {v : V' // col' v = false}) : V') := by
      intro x
      have h3 : (pointGraph G col).dist w x.1 = 3 := x.2
      have h1 := hfp ⟨x.1, by omega⟩
      have h2 := congrArg Subtype.val (hχ ⟨x.1, by omega⟩ h3)
      exact h1.trans h2
    refine ⟨f, ⟨hfcol, hfw, hfO⟩, ?_⟩
    rintro g ⟨hgcol, hgw, hgO⟩
    refine eq_of_agree H H' (i := 2) (Or.inr rfl) hgcol hfcol hgw hfw fun x hx => ?_
    have hgf : ∀ y : oppSet G col w,
        g ((y : {v : V // col v = false}) : V) = f ((y : {v : V // col v = false}) : V) :=
      fun y => (hgO y).trans (hfO y).symm
    by_cases h3 : (pointGraph G col).dist w x = 3
    · exact hgf ⟨x, h3⟩
    have h2 : (pointGraph G col).dist w x = 2 := by
      have := hle x
      omega
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_edge_of_dist_two F h2
    obtain ⟨m, -, am, bm, zm, hz⟩ := edge_line F ha hb hab
    have hga := hgf ⟨a, ha⟩
    have hgb := hgf ⟨b, hb⟩
    have hab' : (a : V) ≠ b := fun e => hab.ne (Subtype.ext e)
    have haz : (a : V) ≠ z a b := fun e => by rw [Subtype.ext e, hz] at ha; omega
    have hbz : (b : V) ≠ z a b := fun e => by rw [Subtype.ext e, hz] at hb; omega
    have hcol : col' (f a) = col' (f b) :=
      (hfcol a).trans (a.2.trans (b.2.symm.trans (hfcol b).symm))
    have hgm : g m = f m := eq_of_adj_adj H' col' (fun e => hab' (f.injective e)) hcol
      (by rw [← hga]; exact g.map_adj_iff.mpr am) (by rw [← hgb]; exact g.map_adj_iff.mpr bm)
      (f.map_adj_iff.mpr am) (f.map_adj_iff.mpr bm)
    have hN : G'.neighborFinset (f m) = {f a, f b, f (z a b)} := neighborFinset_eq H'
      (f.map_adj_iff.mpr am) (f.map_adj_iff.mpr bm) (f.map_adj_iff.mpr zm)
      (fun e => hab' (f.injective e)) (fun e => haz (f.injective e)) (fun e => hbz (f.injective e))
    have hmem : g (z a b) ∈ G'.neighborFinset (f m) := by
      rw [← hgm]
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (g.map_adj_iff.mpr zm).symm
    rw [hN] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with e | e | e
    · exact absurd (g.injective (e.trans hga.symm)).symm haz
    · exact absurd (g.injective (e.trans hgb.symm)).symm hbz
    · exact e
  refine ⟨?_, hb⟩
  obtain ⟨-, hiso, hadj, -⟩ := periodic_point_opposite_graph_recognition_and_automorphism_bound G H
    col w ℓ hℓ hwℓ p hpℓ hpw hp z q c ε hdata hper
  obtain ⟨-, hiso', hadj', -⟩ := periodic_point_opposite_graph_recognition_and_automorphism_bound
    G' H' col' w' ℓ' hℓ' hwℓ' p' hpℓ' hpw' hp' z' q' c' ε' hdata' hper'
  obtain ⟨x₀, hx₀, -⟩ := hper
  obtain ⟨y₀, hy₀, -⟩ := hper'
  obtain ⟨ψ₁, ⟨-, hψ₁⟩, -⟩ := hiso (x₀ 0) (hx₀.2.1 0)
  obtain ⟨ψ₂, ⟨-, hψ₂⟩, -⟩ := hiso' (y₀ 0) (hy₀.2.1 0)
  have hφadj : ∀ a b : oppSet G col w,
      (oppGraph G' col' w').Adj (ψ₂ (ψ₁.symm a)) (ψ₂ (ψ₁.symm b)) ↔ (oppGraph G col w).Adj a b := by
    intro a b
    refine (hadj' ψ₂ hψ₂ (ψ₁.symm a) (ψ₁.symm b)).symm.trans
      ((hadj ψ₁ hψ₁ (ψ₁.symm a) (ψ₁.symm b)).trans ?_)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let φ : oppGraph G col w ≃g oppGraph G' col' w' := ⟨ψ₁.symm.trans ψ₂, fun {a b} => hφadj a b⟩
  have hφ : ∀ a b, (oppGraph G col w).Adj a b → c' (φ a) (φ b) = c a b := by
    intro a b hab
    have h1 := (hψ₁ (c a b) (ψ₁.symm a) (ψ₁.symm b)).mpr (by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact ⟨hab, rfl⟩)
    exact ((hψ₂ (c a b) _ _).mp h1).2
  obtain ⟨f, ⟨hfcol, hfw, -⟩, -⟩ := hb φ hφ
  exact ⟨f, hfcol, hfw⟩

end CFSG.Combinatorics.OuterLayer

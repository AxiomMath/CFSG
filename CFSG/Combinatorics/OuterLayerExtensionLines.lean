module

public import CFSG.Combinatorics.OuterLayerExtensionSupport
public import CFSG.Combinatorics.HexagonLayersSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers

namespace CFSG.Combinatorics.OuterLayer

universe u u'

section OneFrame

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem eq_of_adj_adj (H : MooreHyp G) (col : G.Coloring Bool) {a b m m' : V} (hab : a ≠ b)
    (hc : col a = col b) (ha : G.Adj a m) (hb : G.Adj b m) (ha' : G.Adj a m')
    (hb' : G.Adj b m') : m = m' :=
  pred_unique H.cyc H.conn (k := 1) (by norm_num)
    (show G.dist a b = 1 + 1 from dist_eq_two_of_adj_adj H.conn col hab hc ha hb) hb hb'
    (SimpleGraph.dist_eq_one_iff_adj.mpr ha) (SimpleGraph.dist_eq_one_iff_adj.mpr ha')

theorem eq_of_triangle (H : MooreHyp G) (col : G.Coloring Bool) {a b c m₁ m₂ m₃ : V}
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (hcab : col a = col b) (hcbc : col b = col c)
    (ha₁ : G.Adj a m₁) (hb₁ : G.Adj b m₁) (hb₂ : G.Adj b m₂) (hc₂ : G.Adj c m₂)
    (hc₃ : G.Adj c m₃) (ha₃ : G.Adj a m₃) : m₁ = m₂ := by
  by_contra h12
  have dab : G.dist a b = 2 := dist_eq_two_of_adj_adj H.conn col hab hcab ha₁ hb₁
  have dac : G.dist a c = 2 :=
    dist_eq_two_of_adj_adj H.conn col hca.symm (hcab.trans hcbc) ha₃ hc₃
  have ham₂ : ¬ G.Adj a m₂ := fun h => h12 (eq_of_adj_adj H col hab hcab ha₁ hb₁ h hb₂)
  have dam₂ : G.dist a m₂ = 2 + 1 := by
    rcases dist_adj H.conn col hb₂ a with h | h
    · omega
    · exact absurd (SimpleGraph.dist_eq_one_iff_adj.mp (by omega)) ham₂
  exact hbc (pred_unique H.cyc H.conn (k := 2) (by norm_num) dam₂ hb₂.symm hc₂.symm dab dac)

variable {col : G.Coloring Bool} {w : {v : V // col v = false}}

theorem exists_three_pts (H : MooreHyp G) {j : ℕ} (m : (outerSystem G col w j).Ln) :
    ∃ a b c : (outerSystem G col w j).Pt, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
      G.neighborFinset m.1 = {a.1.1, b.1.1, c.1.1} := by
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ := Finset.card_eq_three.mp
    (show (G.neighborFinset m.1).card = 3 by
      rw [SimpleGraph.card_neighborFinset_eq_degree, H.deg])
  have hadj : ∀ {t : V}, t ∈ ({a, b, c} : Finset V) → G.Adj t m.1 := fun ht =>
    ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; exact ht)).symm
  have hcol : ∀ {t : V}, G.Adj t m.1 → col t = false := fun ht => col_eq_false_of_adj col m.2.1 ht
  have pt : ∀ t : V, G.Adj t m.1 → ∃ x : (outerSystem G col w j).Pt, x.1.1 = t := fun t ht =>
    ⟨⟨⟨t, hcol ht⟩, m.2.2 ⟨t, hcol ht⟩ ht⟩, rfl⟩
  obtain ⟨x, hx⟩ := pt a (hadj (by simp))
  obtain ⟨y, hy⟩ := pt b (hadj (by simp))
  obtain ⟨z, hz⟩ := pt c (hadj (by simp))
  refine ⟨x, y, z, fun e => hab ?_, fun e => hbc ?_, fun e => hac ?_, by rw [hx, hy, hz, hN]⟩
  · rw [← hx, ← hy, e]
  · rw [← hy, ← hz, e]
  · rw [← hx, ← hz, e]

end OneFrame

section TwoFrames

variable {V : Type u} {V' : Type u'} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [Fintype V'] [DecidableEq V'] {G' : SimpleGraph V'} [DecidableRel G'.Adj]
  {col : G.Coloring Bool} {col' : G'.Coloring Bool} {w : {v : V // col v = false}}
  {w' : {v : V' // col' v = false}}

theorem exists_image_line (H : MooreHyp G) (H' : MooreHyp G') {j : ℕ}
    (φ : (outerSystem G col w j).Pt → (outerSystem G' col' w' j).Pt)
    (hφ : ∀ x y : (outerSystem G col w j).Pt, (outerGraph G col w j).Adj x.1 y.1 →
      (outerGraph G' col' w' j).Adj (φ x).1 (φ y).1)
    (m : (outerSystem G col w j).Ln) :
    ∃ m' : (outerSystem G' col' w' j).Ln, ∀ x : (outerSystem G col w j).Pt,
      G.Adj x.1.1 m.1 → G'.Adj (φ x).1.1 m'.1 := by
  obtain ⟨a, b, c, hab, hbc, hca, hN⟩ := exists_three_pts H m
  have hmem : ∀ {t : V}, t ∈ ({a.1.1, b.1.1, c.1.1} : Finset V) → G.Adj t m.1 := fun ht =>
    ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; exact ht)).symm
  have adj : ∀ {x y : (outerSystem G col w j).Pt}, x ≠ y → G.Adj x.1.1 m.1 → G.Adj y.1.1 m.1 →
      (outerGraph G' col' w' j).Adj (φ x).1 (φ y).1 := fun h hx hy =>
    hφ _ _ (outerGraph_adj.mpr ⟨fun e => h (Subtype.ext e), m.1, m.2, hx, hy⟩)
  obtain ⟨hab', m₁, hm₁, am₁, bm₁⟩ :=
    outerGraph_adj.mp (adj hab (hmem (by simp)) (hmem (by simp)))
  obtain ⟨hbc', m₂, -, bm₂, cm₂⟩ := outerGraph_adj.mp (adj hbc (hmem (by simp)) (hmem (by simp)))
  obtain ⟨hca', m₃, -, cm₃, am₃⟩ := outerGraph_adj.mp (adj hca (hmem (by simp)) (hmem (by simp)))
  have hV : ∀ {x y : {v : V' // col' v = false}}, x ≠ y → (x : V') ≠ y :=
    fun h e => h (Subtype.ext e)
  have h12 : m₁ = m₂ := eq_of_triangle H' col' (hV hab') (hV hbc') (hV hca')
    ((φ a).1.2.trans (φ b).1.2.symm) ((φ b).1.2.trans (φ c).1.2.symm) am₁ bm₁ bm₂ cm₂ cm₃ am₃
  refine ⟨⟨m₁, hm₁⟩, fun x hx => ?_⟩
  have hxN : x.1.1 ∈ G.neighborFinset m.1 := (SimpleGraph.mem_neighborFinset _ _ _).mpr hx.symm
  rw [hN] at hxN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxN
  rcases hxN with h | h | h
  · rw [show x = a from Subtype.ext (Subtype.ext h)]
    exact am₁
  · rw [show x = b from Subtype.ext (Subtype.ext h)]
    exact bm₁
  · rw [show x = c from Subtype.ext (Subtype.ext h)]
    show G'.Adj (φ c).1.1 m₁
    rw [h12]
    exact cm₂

theorem exists_iso_of_pts (H : MooreHyp G) (H' : MooreHyp G') {j : ℕ}
    (φ : (outerSystem G col w j).Pt ≃ (outerSystem G' col' w' j).Pt)
    (hφ : ∀ x y : (outerSystem G col w j).Pt,
      (outerGraph G' col' w' j).Adj (φ x).1 (φ y).1 ↔ (outerGraph G col w j).Adj x.1 y.1)
    (hmk : ∀ x, x ∈ (outerSystem G col w j).marked ↔ φ x ∈ (outerSystem G' col' w' j).marked) :
    ∃ χ : (outerSystem G col w j).Iso (outerSystem G' col' w' j), χ.pts = φ := by
  have hφ' : ∀ x y : (outerSystem G' col' w' j).Pt, (outerGraph G' col' w' j).Adj x.1 y.1 →
      (outerGraph G col w j).Adj (φ.symm x).1 (φ.symm y).1 := by
    intro x y h
    rw [← hφ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h
  choose μ hμ using exists_image_line H H' φ (fun x y h => (hφ x y).mpr h)
  choose μ' hμ' using exists_image_line H' H φ.symm hφ'
  have hinv : ∀ m, μ' (μ m) = m := by
    intro m
    obtain ⟨a, b, _, hab, -, -, hN⟩ := exists_three_pts H m
    have am : G.Adj a.1.1 m.1 :=
      ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
    have bm : G.Adj b.1.1 m.1 :=
      ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
    have a' := hμ' (μ m) (φ a) (hμ m a am)
    have b' := hμ' (μ m) (φ b) (hμ m b bm)
    rw [Equiv.symm_apply_apply] at a' b'
    exact Subtype.ext (eq_of_adj_adj H col (fun e => hab (Subtype.ext (Subtype.ext e)))
      (a.1.2.trans b.1.2.symm) a' b' am bm)
  have hinv' : ∀ m, μ (μ' m) = m := by
    intro m
    obtain ⟨a, b, _, hab, -, -, hN⟩ := exists_three_pts H' m
    have am : G'.Adj a.1.1 m.1 :=
      ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
    have bm : G'.Adj b.1.1 m.1 :=
      ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
    have a' := hμ (μ' m) (φ.symm a) (hμ' m a am)
    have b' := hμ (μ' m) (φ.symm b) (hμ' m b bm)
    rw [Equiv.apply_symm_apply] at a' b'
    exact Subtype.ext (eq_of_adj_adj H' col' (fun e => hab (Subtype.ext (Subtype.ext e)))
      (a.1.2.trans b.1.2.symm) a' b' am bm)
  refine ⟨⟨φ, ⟨μ, μ', hinv, hinv'⟩, fun x m => ⟨hμ m x, fun h => ?_⟩, hmk⟩, rfl⟩
  have := hμ' (μ m) (φ x) h
  rwa [Equiv.symm_apply_apply, hinv] at this

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype V'] [DecidableEq V']
  [DecidableRel G'.Adj] in
theorem exists_vertexMap (χ : (outerSystem G col w 0).Iso (outerSystem G' col' w' 0)) :
    ∃ F : V → V', (∀ x : (outerSystem G col w 0).Pt, F x.1.1 = (χ.pts x).1.1) ∧
      ∀ m : (outerSystem G col w 0).Ln, F m.1 = (χ.lines m).1 := by
  have key : ∀ v : V, ∃ v' : V', (∀ x : (outerSystem G col w 0).Pt, x.1.1 = v →
      v' = (χ.pts x).1.1) ∧ ∀ m : (outerSystem G col w 0).Ln, m.1 = v → v' = (χ.lines m).1 := by
    intro v
    cases hv : col v with
    | false =>
      refine ⟨(χ.pts ⟨⟨v, hv⟩, Nat.zero_le _⟩).1.1, fun x hx => ?_, fun m hm => ?_⟩
      · rw [show x = ⟨⟨v, hv⟩, Nat.zero_le _⟩ from Subtype.ext (Subtype.ext hx)]
      · exfalso
        have h1 := m.2.1
        rw [hm, hv] at h1
        exact Bool.false_ne_true h1
    | true =>
      refine ⟨(χ.lines ⟨v, hv, fun _ _ => Nat.zero_le _⟩).1, fun x hx => ?_, fun m hm => ?_⟩
      · exfalso
        have h1 := x.1.2
        rw [hx, hv] at h1
        exact Bool.false_ne_true h1.symm
      · rw [show m = ⟨v, hv, fun _ _ => Nat.zero_le _⟩ from Subtype.ext hm]
  choose F hF using key
  exact ⟨F, fun x => (hF _).1 x rfl, fun m => (hF _).2 m rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype V'] [DecidableEq V']
  [DecidableRel G'.Adj] in
theorem exists_graphIso (χ : (outerSystem G col w 0).Iso (outerSystem G' col' w' 0)) :
    ∃ f : G ≃g G', (∀ v, col' (f v) = col v) ∧
      (∀ x : (outerSystem G col w 0).Pt, f x.1.1 = (χ.pts x).1.1) ∧
      ∀ m : (outerSystem G col w 0).Ln, f m.1 = (χ.lines m).1 := by
  obtain ⟨F, hFp, hFl⟩ := exists_vertexMap χ
  obtain ⟨F', hF'p, hF'l⟩ := exists_vertexMap χ.symm
  have hpt : ∀ {v : V}, col v = false → ∃ x : (outerSystem G col w 0).Pt, x.1.1 = v :=
    fun {v} hv => ⟨⟨⟨v, hv⟩, Nat.zero_le _⟩, rfl⟩
  have hln : ∀ {v : V}, col v = true → ∃ m : (outerSystem G col w 0).Ln, m.1 = v :=
    fun {v} hv => ⟨⟨v, hv, fun _ _ => Nat.zero_le _⟩, rfl⟩
  have hpt' : ∀ {v : V'}, col' v = false → ∃ x : (outerSystem G' col' w' 0).Pt, x.1.1 = v :=
    fun {v} hv => ⟨⟨⟨v, hv⟩, Nat.zero_le _⟩, rfl⟩
  have hln' : ∀ {v : V'}, col' v = true → ∃ m : (outerSystem G' col' w' 0).Ln, m.1 = v :=
    fun {v} hv => ⟨⟨v, hv, fun _ _ => Nat.zero_le _⟩, rfl⟩
  have hcol : ∀ v, col' (F v) = col v := by
    intro v
    cases hv : col v with
    | false =>
      obtain ⟨x, rfl⟩ := hpt hv
      rw [hFp x]
      exact (χ.pts x).1.2
    | true =>
      obtain ⟨m, rfl⟩ := hln hv
      rw [hFl m]
      exact (χ.lines m).2.1
  have hleft : ∀ v, F' (F v) = v := by
    intro v
    cases hv : col v with
    | false =>
      obtain ⟨x, rfl⟩ := hpt hv
      rw [hFp x, hF'p, MarkedIncidenceSystem.Iso.symm_pts_apply]
    | true =>
      obtain ⟨m, rfl⟩ := hln hv
      rw [hFl m, hF'l, MarkedIncidenceSystem.Iso.symm_lines_apply]
  have hright : ∀ v, F (F' v) = v := by
    intro v
    cases hv : col' v with
    | false =>
      obtain ⟨x, rfl⟩ := hpt' hv
      rw [hF'p x, hFp, MarkedIncidenceSystem.Iso.pts_symm_apply]
    | true =>
      obtain ⟨m, rfl⟩ := hln' hv
      rw [hF'l m, hFl, MarkedIncidenceSystem.Iso.lines_symm_apply]
  have hadj : ∀ u v, col u = false → col v = true → (G'.Adj (F u) (F v) ↔ G.Adj u v) := by
    intro u v hu hv
    obtain ⟨x, rfl⟩ := hpt hu
    obtain ⟨m, rfl⟩ := hln hv
    rw [hFp x, hFl m]
    exact (χ.inc_iff x m).symm
  refine ⟨⟨⟨F, F', hleft, hright⟩, fun {u v} => ?_⟩, hcol, hFp, hFl⟩
  change G'.Adj (F u) (F v) ↔ G.Adj u v
  cases hu : col u <;> cases hv : col v
  · refine iff_of_false (fun h => ?_) (fun h => ?_)
    · have := col'.valid h
      rw [hcol, hcol, hu, hv] at this
      exact this rfl
    · have := col.valid h
      rw [hu, hv] at this
      exact this rfl
  · exact hadj u v hu hv
  · rw [G'.adj_comm, G.adj_comm]
    exact hadj v u hv hu
  · refine iff_of_false (fun h => ?_) (fun h => ?_)
    · have := col'.valid h
      rw [hcol, hcol, hu, hv] at this
      exact this rfl
    · have := col.valid h
      rw [hu, hv] at this
      exact this rfl

end TwoFrames

end CFSG.Combinatorics.OuterLayer

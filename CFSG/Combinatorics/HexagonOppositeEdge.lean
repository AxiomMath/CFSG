module

public import CFSG.Combinatorics.HexagonOppositeEdgeSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers

namespace CFSG.Combinatorics.HexagonOppositeEdge

theorem opposite_edge_equal_label_separation_and_four_path_repeat {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (H : MooreHyp G)
    (col : G.Coloring Bool) (w : {v : V // col v = false}) (ℓ : Fin 3 → V)
    (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    (p : Fin 3 → Fin 2 → {v : V // col v = false}) (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i))
    (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2) :
    let Γ : SimpleGraph {v : V // col v = false} := pointGraph G col
    let O : Set {v : V // col v = false} := {x | Γ.dist w x = 3}
    (∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y →
      (∀ m : V, G.Adj (x : V) m → G.Adj (y : V) m →
        G.neighborFinset m = {(x : V), (y : V), (z x y : V)}) ∧
      (∀ t, Γ.Adj (z x y) t ∧ Γ.dist w t = 1 ↔ t = q x y) ∧ q x y = p (c x y) (ε x y)) →
    (∀ x ∈ O, ∀ y ∈ O, ∀ x' ∈ O, ∀ y' ∈ O, Γ.Adj x y → Γ.Adj x' y' →
      s(x, y) ≠ s(x', y') → q x y = q x' y' →
        Disjoint ({x, y} : Finset {v : V // col v = false}) {x', y'} ∧
          ∀ a ∈ ({x, y} : Finset {v : V // col v = false}),
            ∀ b ∈ ({x', y'} : Finset {v : V // col v = false}), ¬ Γ.Adj a b) ∧
    (∀ v₀ ∈ O, ∀ v₁ ∈ O, ∀ v₂ ∈ O, ∀ v₃ ∈ O, ∀ v₄ ∈ O,
      Γ.Adj v₀ v₁ → Γ.Adj v₁ v₂ → Γ.Adj v₂ v₃ → Γ.Adj v₃ v₄ → [v₀, v₁, v₂, v₃, v₄].Nodup →
        c v₀ v₁ = c v₃ v₄ → q v₀ v₁ = q v₃ v₄) := by
  intro Γ O hdata
  have hd : ∀ (a b : {v : V // col v = false}) (k : ℕ),
      Γ.dist a b = k ↔ G.dist (a : V) b = 2 * k := point_dist_eq_iff H.conn col
  have hO : ∀ x : {v : V // col v = false}, x ∈ O ↔ G.dist (w : V) x = 6 := fun x => hd w x 3
  have hedge : ∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y → ∃ m : V,
      G.neighborFinset m = {(x : V), (y : V), (z x y : V)} ∧ G.Adj (x : V) m ∧
      G.Adj (y : V) m ∧ G.dist (w : V) (z x y) = 4 ∧ G.dist (q x y : V) x = 4 ∧
      G.dist (q x y : V) y = 4 ∧ G.dist (q x y : V) m = 3 := fun x hx y hy hxy =>
    edge_data H col hx hy hxy (hdata x hx y hy hxy).1
      (((hdata x hx y hy hxy).2.1 (q x y)).mpr rfl)
  have hsep : ∀ x ∈ O, ∀ y ∈ O, ∀ x' ∈ O, ∀ y' ∈ O, Γ.Adj x y → Γ.Adj x' y' →
      s(x, y) ≠ s(x', y') → q x y = q x' y' →
        Disjoint ({x, y} : Finset {v : V // col v = false}) {x', y'} ∧
          ∀ a ∈ ({x, y} : Finset {v : V // col v = false}),
            ∀ b ∈ ({x', y'} : Finset {v : V // col v = false}), ¬ Γ.Adj a b := by
    intro x hx y hy x' hx' y' hy' hxy hxy' hne hqq
    obtain ⟨m, hN, hxm, hym, hz4, hqx, hqy, hqm⟩ := hedge x hx y hy hxy
    obtain ⟨m', -, hxm', hym', -, hqx', hqy', hqm'⟩ := hedge x' hx' y' hy' hxy'
    rw [← hqq] at hqx' hqy' hqm'
    have hend : ∀ a ∈ ({x, y} : Finset {v : V // col v = false}),
        G.Adj (a : V) m ∧ G.dist (q x y : V) a = 4 := by
      intro a ha
      rw [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      exacts [⟨hxm, hqx⟩, ⟨hym, hqy⟩]
    have hend' : ∀ b ∈ ({x', y'} : Finset {v : V // col v = false}),
        G.Adj (b : V) m' ∧ G.dist (q x y : V) b = 4 ∧ G.dist (w : V) b = 6 := by
      intro b hb
      rw [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      exacts [⟨hxm', hqx', (hO _).mp hx'⟩, ⟨hym', hqy', (hO _).mp hy'⟩]
    have hmm : m ≠ m' := by
      intro hmm
      apply hne
      have hfar : ∀ b ∈ ({x', y'} : Finset {v : V // col v = false}), b = x ∨ b = y := by
        intro b hb
        have hbN : (b : V) ∈ G.neighborFinset m :=
          (SimpleGraph.mem_neighborFinset _ _ _).mpr (hmm ▸ (hend' b hb).1).symm
        rw [hN] at hbN
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbN
        rcases hbN with h | h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
        · have hb6 := (hend' b hb).2.2
          rw [h] at hb6
          omega
      rcases hfar x' (by simp) with h1 | h1 <;> rcases hfar y' (by simp) with h2 | h2
      · exact absurd (h1.trans h2.symm) hxy'.ne
      · rw [h1, h2]
      · rw [h1, h2, Sym2.eq_swap]
      · exact absurd (h1.trans h2.symm) hxy'.ne
    refine ⟨Finset.disjoint_left.mpr ?_, fun a ha b hb hab => hmm ?_⟩
    · intro a ha ha'
      exact hmm (line_eq_of_dist_le_three H col (hend a ha).2 (hend a ha).1 (hend' a ha').1
        hqm.le hqm'.le)
    · obtain ⟨n, han, hbn⟩ :=
        exists_adj_adj_of_dist_eq_two H.conn ((point_adj_iff H.conn col a b).mp hab)
      have hn := dist_eq_three_of_adj_adj H col (hend a ha).2 (hend' b hb).2.1
        (fun h => hab.ne (Subtype.ext h)) han hbn
      exact (line_eq_of_dist_le_three H col (hend a ha).2 (hend a ha).1 han hqm.le hn.le).trans
        (line_eq_of_dist_le_three H col (hend' b hb).2.1 (hend' b hb).1 hbn hqm'.le hn.le).symm
  refine ⟨hsep, ?_⟩
  intro v₀ h₀ v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ h01 h12 h23 h34 hnd hc
  obtain ⟨u, hu, h2u, hcu⟩ := exists_adj_colour_eq H col hℓ hwℓ hpℓ hpw hp hdata h₂ (c v₀ v₁)
  have h20 : v₂ ≠ v₀ := by
    rintro rfl
    simp at hnd
  have h21 : v₂ ≠ v₁ := by
    rintro rfl
    simp at hnd
  have h23' : v₂ ≠ v₃ := by
    rintro rfl
    simp at hnd
  have h24 : v₂ ≠ v₄ := by
    rintro rfl
    simp at hnd
  have hne₁ : s(v₂, u) ≠ s(v₀, v₁) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
    exacts [h20 h', h21 h']
  have hne₂ : s(v₂, u) ≠ s(v₃, v₄) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
    exacts [h23' h', h24 h']
  have hq₁ : q v₂ u ≠ q v₀ v₁ := fun h =>
    (hsep v₂ h₂ u hu v₀ h₀ v₁ h₁ h2u h01 hne₁ h).2 v₂ (by simp) v₁ (by simp) h12.symm
  have hq₂ : q v₂ u ≠ q v₃ v₄ := fun h =>
    (hsep v₂ h₂ u hu v₃ h₃ v₄ h₄ h2u h34 hne₂ h).2 v₂ (by simp) v₃ (by simp) h23
  have hl₀ := (hdata v₀ h₀ v₁ h₁ h01).2.2
  have hl₂ := (hdata v₂ h₂ u hu h2u).2.2
  have hl₃ := (hdata v₃ h₃ v₄ h₄ h34).2.2
  rw [hcu] at hl₂
  rw [← hc] at hl₃
  have hfin : ∀ a b d : Fin 2, d ≠ a → d ≠ b → a = b := by decide
  rw [hl₀, hl₃, hfin (ε v₀ v₁) (ε v₃ v₄) (ε v₂ u) (fun h => hq₁ (by rw [hl₂, hl₀, h]))
    (fun h => hq₂ (by rw [hl₂, hl₃, h]))]

end CFSG.Combinatorics.HexagonOppositeEdge

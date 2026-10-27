module

public import Mathlib.Combinatorics.SimpleGraph.Girth

public section

namespace CFSG.Geometry.GeneralizedPolygons

open SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

structure IsGeneralizedPolygon (m : ℕ) : Prop where
  connected : G.Connected
  isBipartite : G.IsBipartite
  diam_eq : G.diam = m
  girth_eq : G.girth = 2 * m

@[expose] def IsThick [Fintype V] [DecidableRel G.Adj] : Prop := ∀ v, 3 ≤ G.degree v

variable {G}

theorem eq_iff_even_length (c : G.Coloring (Fin 2)) {u v : V} (p : G.Walk u v) :
    c u = c v ↔ Even p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have key : ∀ x y z : Fin 2, x ≠ y → (x = z ↔ ¬ y = z) := by decide
    rw [Walk.length_cons, Nat.even_add_one, ← ih]
    exact key _ _ _ (c.valid h)

variable {m : ℕ}

namespace IsGeneralizedPolygon

variable (hG : IsGeneralizedPolygon G m)
include hG

theorem dist_le (hm : m ≠ 0) (x y : V) : G.dist x y ≤ m := by
  rw [← hG.diam_eq]
  exact dist_le_diam (ediam_ne_top_of_diam_ne_zero (hG.diam_eq ▸ hm))

theorem eq_iff_even_dist (c : G.Coloring (Fin 2)) (x y : V) :
    c x = c y ↔ Even (G.dist x y) := by
  obtain ⟨p, hp⟩ := hG.connected.exists_walk_length_eq_dist x y
  rw [eq_iff_even_length c p, hp]

theorem dist_adj {v z : V} (h : G.Adj v z) (y : V) :
    G.dist y z = G.dist y v + 1 ∨ G.dist y v = G.dist y z + 1 := by
  obtain ⟨c⟩ := hG.isBipartite
  have h1 := h.diff_dist_adj (u := y)
  have key : ∀ a b x : Fin 2, a ≠ b → (x = a ↔ ¬ x = b) := by decide
  have hne : G.dist y z ≠ G.dist y v := by
    intro e
    have := key _ _ (c y) (c.valid h)
    rw [hG.eq_iff_even_dist c y v, hG.eq_iff_even_dist c y z, e] at this
    exact (iff_not_self this).elim
  omega

theorem exists_adj_dist_succ {y v : V} (hv : 0 < G.dist y v) :
    ∃ z, G.Adj v z ∧ G.dist y z + 1 = G.dist y v := by
  obtain ⟨p, hp⟩ := hG.connected.exists_walk_length_eq_dist v y
  cases p with
  | nil => simp at hv
  | @cons _ z _ h p =>
    refine ⟨z, h, ?_⟩
    have h1 := SimpleGraph.dist_le p
    have h2 : G.dist v y ≤ G.dist v z + G.dist z y := hG.connected.dist_triangle
    rw [dist_eq_one_iff_adj.mpr h] at h2
    rw [Walk.length_cons] at hp
    rw [dist_comm (v := v), dist_comm (u := y)]
    omega

theorem eq_of_adj_of_dist_succ {y v z₁ z₂ : V} (hv : G.dist y v < m) (h₁ : G.Adj v z₁)
    (h₂ : G.Adj v z₂) (hd₁ : G.dist y z₁ + 1 = G.dist y v)
    (hd₂ : G.dist y z₂ + 1 = G.dist y v) : z₁ = z₂ := by
  by_contra hne
  obtain ⟨p₁, -, hl₁⟩ := hG.connected.exists_path_of_dist z₁ y
  obtain ⟨p₂, -, hl₂⟩ := hG.connected.exists_path_of_dist z₂ y
  have e₁ : G.dist z₁ y = G.dist y z₁ := dist_comm
  have e₂ : G.dist z₂ y = G.dist y z₂ := dist_comm
  have e₃ : G.dist v y = G.dist y v := dist_comm
  have hq₁ : (Walk.cons h₁ p₁).IsPath := (Walk.cons h₁ p₁).isPath_of_length_eq_dist (by
    rw [Walk.length_cons, hl₁]
    omega)
  have hq₂ : (Walk.cons h₂ p₂).IsPath := (Walk.cons h₂ p₂).isPath_of_length_eq_dist (by
    rw [Walk.length_cons, hl₂]
    omega)
  have hne' : Walk.cons h₁ p₁ ≠ Walk.cons h₂ p₂ := fun e => hne (by
    have := congrArg (fun q : G.Walk v y => q.getVert 1) e
    simpa [Walk.getVert_cons_succ] using this)
  obtain ⟨w, -, -, c, hc, hcl⟩ := hq₁.exists_isCycle_length_le_add_of_ne hq₂ hne'
  have h3 := hc.girth_le_length
  rw [hG.girth_eq] at h3
  simp only [Walk.length_cons] at hcl
  omega

theorem dist_succ_of_dist_eq (hm : m ≠ 0) {y v z : V} (hv : G.dist y v = m) (h : G.Adj v z) :
    G.dist y z + 1 = G.dist y v := by
  rcases hG.dist_adj h y with h' | h'
  · have := hG.dist_le hm y z
    omega
  · omega

variable [Fintype V] [DecidableRel G.Adj]

theorem exists_dist_eq (hthick : IsThick G) {w u : V} (hwu : G.Adj w u) :
    ∀ k, 1 ≤ k → k ≤ m → ∃ y, G.dist w y = k ∧ G.dist u y + 1 = k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _
    exact ⟨u, dist_eq_one_iff_adj.mpr hwu, by simp⟩
  | succ k hk ih =>
    intro hkm
    obtain ⟨y, hwy, huy⟩ := ih (by omega)
    have h3 := hthick y
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1
      (show 1 < (G.neighborFinset y).card by rw [card_neighborFinset_eq_degree]; omega)
    rw [mem_neighborFinset] at ha hb
    obtain ⟨z, hz, hzw⟩ : ∃ z, G.Adj y z ∧ G.dist w z = G.dist w y + 1 := by
      rcases hG.dist_adj ha w with h | h
      · exact ⟨a, ha, h⟩
      rcases hG.dist_adj hb w with h' | h'
      · exact ⟨b, hb, h'⟩
      exact absurd (hG.eq_of_adj_of_dist_succ (by omega) ha hb h.symm h'.symm) hab
    refine ⟨z, by omega, ?_⟩
    rcases hG.dist_adj hz u with h | h
    · omega
    · have h1 : G.dist w z ≤ G.dist w u + G.dist u z := hG.connected.dist_triangle
      rw [dist_eq_one_iff_adj.mpr hwu] at h1
      omega

end IsGeneralizedPolygon

end CFSG.Geometry.GeneralizedPolygons

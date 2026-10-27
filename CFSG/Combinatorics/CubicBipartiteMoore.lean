module

public import CFSG.Combinatorics.CubicBipartiteMooreSupport

public section

open Finset

namespace CFSG.Combinatorics.CubicBipartiteMoore

theorem cubic_bipartite_moore_equality_and_nearest_point_property {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 126)
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 3) (col : G.Coloring Bool)
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length) :
    let P : Finset V := univ.filter fun v => col v = false
    let L : Finset V := univ.filter fun v => col v = true
    let Γ : SimpleGraph {v : V // col v = false} :=
      SimpleGraph.fromRel fun p q => ∃ ℓ : V, col ℓ = true ∧ G.Adj p ℓ ∧ G.Adj q ℓ
    G.girth = 12 ∧ G.diam = 6 ∧
    (∀ u v : V, G.dist u v < 6 → ∃! p : G.Walk u v, p.IsPath ∧ p.length = G.dist u v) ∧
    (∀ (v : V) (k : Fin 7),
      (univ.filter fun w => G.dist v w = k).card = ![1, 3, 6, 12, 24, 48, 32] k) ∧
    P.card = 63 ∧ L.card = 63 ∧
    ((∀ ℓ ∈ L, (G.neighborFinset ℓ).card = 3 ∧ G.neighborFinset ℓ ⊆ P) ∧
      (∀ p ∈ P, (G.neighborFinset p).card = 3 ∧ G.neighborFinset p ⊆ L) ∧
      G.girth = 12 ∧ G.diam = 6) ∧
    (∀ (p : {v : V // col v = false}) (k : Fin 4),
      (univ.filter fun q => Γ.dist p q = k).card = ![1, 6, 24, 32] k) ∧
    Γ.Connected ∧ Γ.diam = 3 ∧
    (∀ (p : {v : V // col v = false}) (ℓ : V), col ℓ = true →
      ∃! q : {v : V // col v = false}, G.Adj (q : V) ℓ ∧
        ∀ q' : {v : V // col v = false}, G.Adj (q' : V) ℓ → Γ.dist p q ≤ Γ.dist p q') ∧
    (∀ p q : {v : V // col v = false}, p ≠ q → ∀ ℓ ℓ' : V,
      G.Adj (p : V) ℓ → G.Adj (q : V) ℓ → G.Adj (p : V) ℓ' → G.Adj (q : V) ℓ' → ℓ = ℓ') := by
  intro P L Γ
  obtain ⟨v₀⟩ := hconn.nonempty
  have hgirth := girth_eq_twelve hcyc hconn col hdeg hcard
  have hdiam := diam_eq_six hcyc hconn col hdeg hcard
  have hpar : ∀ (p w : V), col p = false → (Even (G.dist p w) ↔ col w = false) := by
    intro p w hp
    rw [even_dist_iff hconn col p w, Bool.coe_iff_coe, hp, eq_comm]
  have hΓ : ∀ p q : {v : V // col v = false}, Γ.dist p q = G.dist (p : V) q / 2 ∧
      Γ.Reachable p q := point_dist hconn col
  have hPL : P.card = 63 ∧ L.card = 63 := by
    obtain ⟨hsame, hother⟩ := card_color_classes hcyc hconn col hdeg hcard v₀
    rcases Bool.eq_false_or_eq_true (col v₀) with h | h
    · rw [h] at hsame hother
      refine ⟨?_, hsame⟩
      rw [← hother]
      exact congrArg Finset.card (Finset.filter_congr fun w _ => by simp)
    · rw [h] at hsame hother
      refine ⟨hsame, ?_⟩
      rw [← hother]
      exact congrArg Finset.card (Finset.filter_congr fun w _ => by simp)
  have hPne : Nonempty {v : V // col v = false} := by
    obtain ⟨w, hw⟩ : P.Nonempty := Finset.card_pos.mp (by rw [hPL.1]; norm_num)
    exact ⟨⟨w, (Finset.mem_filter.mp hw).2⟩⟩
  have hΓlayer : ∀ (p : {v : V // col v = false}) (k : ℕ),
      (univ.filter fun q => Γ.dist p q = k).card = (layer G (p : V) (2 * k)).card := by
    intro p k
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext w
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [(hΓ p q).1] at hq
      have heven := (hpar (p : V) q p.2).mpr q.2
      obtain ⟨m, hm⟩ := heven
      omega
    · intro hw
      have hwP : col w = false := (hpar (p : V) w p.2).mp ⟨k, by omega⟩
      refine ⟨⟨w, hwP⟩, ?_, rfl⟩
      rw [(hΓ p ⟨w, hwP⟩).1]
      change G.dist (p : V) w / 2 = k
      omega
  refine ⟨hgirth, hdiam, ?_, ?_, hPL.1, hPL.2, ?_, ?_, ⟨fun p q => (hΓ p q).2⟩, ?_, ?_, ?_⟩
  ·
    intro u v hd
    obtain ⟨p, hp, hpl⟩ := hconn.exists_path_of_dist u v
    refine ⟨p, ⟨hp, hpl⟩, fun q hq => ?_⟩
    exact walk_unique hcyc hconn (G.dist u v) (by omega) u v rfl q p hq.2 hpl
  ·
    intro v k
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, -⟩ := card_layers hcyc hconn col hdeg hcard v
    fin_cases k
    exacts [h0, h1, h2, h3, h4, h5, h6]
  ·
    refine ⟨fun ℓ hℓ => ⟨?_, fun p hp => ?_⟩, fun p hp => ⟨?_, fun ℓ hℓ => ?_⟩, hgirth, hdiam⟩
    · rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
    · rw [SimpleGraph.mem_neighborFinset] at hp
      have hc := col.valid hp
      have hℓ' := (Finset.mem_filter.mp hℓ).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ p, ?_⟩
      rw [hℓ'] at hc
      simpa using hc.symm
    · rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
    · rw [SimpleGraph.mem_neighborFinset] at hℓ
      have hc := col.valid hℓ
      have hp' := (Finset.mem_filter.mp hp).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ ℓ, ?_⟩
      rw [hp'] at hc
      simpa using hc.symm
  ·
    intro p k
    obtain ⟨h0, -, h2, -, h4, -, h6, -⟩ := card_layers hcyc hconn col hdeg hcard (p : V)
    fin_cases k
    · exact (hΓlayer p 0).trans h0
    · exact (hΓlayer p 1).trans h2
    · exact (hΓlayer p 2).trans h4
    · exact (hΓlayer p 3).trans h6
  ·
    obtain ⟨p₀⟩ := hPne
    obtain ⟨y, hy6, -⟩ := exists_dist_six hcyc hconn col hdeg hcard (p₀ : V)
    have hyP : col y = false := (hpar (p₀ : V) y p₀.2).mp ⟨3, by omega⟩
    have hed : Γ.ediam = 3 := by
      apply le_antisymm
      · apply SimpleGraph.ediam_le_of_edist_le
        intro p q
        rw [← (hΓ p q).2.coe_dist_eq_edist, (hΓ p q).1]
        have := dist_le_six hcyc hconn col hdeg hcard (p : V) q
        exact_mod_cast (by omega : G.dist (p : V) q / 2 ≤ 3)
      · calc (3 : ℕ∞) = Γ.edist p₀ ⟨y, hyP⟩ := by
              rw [← (hΓ p₀ ⟨y, hyP⟩).2.coe_dist_eq_edist, (hΓ p₀ ⟨y, hyP⟩).1]
              change (3 : ℕ∞) = ((G.dist (p₀ : V) y / 2 : ℕ) : ℕ∞)
              rw [hy6]
              rfl
          _ ≤ Γ.ediam := SimpleGraph.edist_le_ediam
    rw [SimpleGraph.diam, hed]
    rfl
  ·
    intro p ℓ hℓ
    have hodd : ¬ Even (G.dist (p : V) ℓ) := by
      rw [hpar (p : V) ℓ p.2, hℓ]
      simp
    have hd6 := dist_le_six hcyc hconn col hdeg hcard (p : V) ℓ
    obtain ⟨k, hk⟩ : ∃ k, G.dist (p : V) ℓ = k + 1 := ⟨G.dist (p : V) ℓ - 1, by
      rcases Nat.even_or_odd (G.dist (p : V) ℓ) with h | ⟨m, hm⟩
      · exact absurd h hodd
      · omega⟩
    have hk5 : k + 1 ≤ 5 := by
      by_contra h
      have hk6 : G.dist (p : V) ℓ = 6 := by omega
      exact hodd ⟨3, by omega⟩
    have hkeven : Even k := by
      rcases Nat.even_or_odd k with h | ⟨m, hm⟩
      · exact h
      · exact absurd ⟨m + 1, by omega⟩ hodd
    obtain ⟨q₀, hq₀, hq₀k⟩ := pred_exists hconn hk
    have hq₀P : col q₀ = false := (hpar (p : V) q₀ p.2).mp (hq₀k ▸ hkeven)
    have hnb : ∀ q : V, G.Adj q ℓ → G.dist (p : V) q = k ∨ G.dist (p : V) q = k + 2 := by
      intro q hq
      rcases dist_adj hconn col hq (p : V) with h | h <;> omega
    refine ⟨⟨q₀, hq₀P⟩, ⟨hq₀.symm, fun q' hq' => ?_⟩, fun q₁ ⟨hq₁, hmin⟩ => ?_⟩
    · rw [(hΓ p _).1, (hΓ p q').1]
      change G.dist (p : V) q₀ / 2 ≤ G.dist (p : V) q' / 2
      rcases hnb q' hq' with h | h
      · rw [hq₀k, h]
      · rw [hq₀k, h]
        omega
    · have hm := hmin ⟨q₀, hq₀P⟩ hq₀.symm
      rw [(hΓ p q₁).1, (hΓ p _).1] at hm
      change G.dist (p : V) q₁ / 2 ≤ G.dist (p : V) q₀ / 2 at hm
      have hq₁k : G.dist (p : V) q₁ = k := by
        rcases hnb q₁ hq₁ with h | h
        · exact h
        · obtain ⟨m, hm'⟩ := hkeven
          rw [h, hq₀k] at hm
          omega
      apply Subtype.ext
      exact pred_unique hcyc hconn hk5 hk hq₁.symm hq₀ hq₁k hq₀k
  ·
    intro p q hpq ℓ ℓ' hpℓ hqℓ hpℓ' hqℓ'
    have hqp : G.dist (q : V) p = 2 := by
      have hle : G.dist (q : V) p ≤ 2 := by
        have := SimpleGraph.dist_le (SimpleGraph.Walk.cons hqℓ (SimpleGraph.Walk.cons hpℓ.symm
          SimpleGraph.Walk.nil))
        simpa using this
      have hne0 : G.dist (q : V) p ≠ 0 := by
        intro h0
        exact hpq (Subtype.ext ((hconn.dist_eq_zero_iff).mp h0).symm)
      have hne1 : G.dist (q : V) p ≠ 1 := by
        intro h1
        have hadj := SimpleGraph.dist_eq_one_iff_adj.mp h1
        have hc := col.valid hadj
        rw [q.2, p.2] at hc
        exact hc rfl
      omega
    exact pred_unique hcyc hconn (by norm_num) (show G.dist (q : V) p = 1 + 1 from hqp) hpℓ hpℓ'
      (SimpleGraph.dist_eq_one_iff_adj.mpr hqℓ) (SimpleGraph.dist_eq_one_iff_adj.mpr hqℓ')

end CFSG.Combinatorics.CubicBipartiteMoore

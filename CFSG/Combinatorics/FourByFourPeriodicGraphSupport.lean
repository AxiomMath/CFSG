module

public import CFSG.Combinatorics.FourByFourPeriodicGraph
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Combinatorics.FourByFourPeriodicGraph

@[expose] def translateVertex (t : ZMod 4 × ZMod 4) (p : Vertex) : Vertex :=
  (p.1 + t, p.2)

theorem nbr_translateVertex : ∀ (t : ZMod 4 × ZMod 4) (p : Vertex) (i : Fin 3),
    nbr (translateVertex t p) i = translateVertex t (nbr p i) := by
  decide

theorem translateVertex_injective (t : ZMod 4 × ZMod 4) :
    Function.Injective (translateVertex t) := by
  intro p q h
  have h1 : p.1 + t = q.1 + t := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (add_right_cancel h1) h2

@[expose] def base (e : Fin 2) : Vertex :=
  ((0, 0), e)

theorem eq_translateVertex_base (x : Vertex) : x = translateVertex x.1 (base x.2) :=
  Prod.ext (zero_add x.1).symm rfl

@[expose] def wordPath (x : Vertex) : List (Fin 3) → List Vertex
  | [] => []
  | a :: w => nbr x a :: wordPath (nbr x a) w

@[expose] def wordEnd (x : Vertex) : List (Fin 3) → Vertex
  | [] => x
  | a :: w => wordEnd (nbr x a) w

theorem wordPath_translateVertex (t : ZMod 4 × ZMod 4) :
    ∀ (x : Vertex) (w : List (Fin 3)),
      wordPath (translateVertex t x) w = (wordPath x w).map (translateVertex t)
  | x, [] => rfl
  | x, a :: w => by
    rw [wordPath, wordPath, nbr_translateVertex, wordPath_translateVertex t (nbr x a) w,
      List.map_cons]

theorem wordEnd_translateVertex (t : ZMod 4 × ZMod 4) :
    ∀ (x : Vertex) (w : List (Fin 3)),
      wordEnd (translateVertex t x) w = translateVertex t (wordEnd x w)
  | x, [] => rfl
  | x, a :: w => by
    rw [wordEnd, wordEnd, nbr_translateVertex, wordEnd_translateVertex t (nbr x a) w]

theorem of_base (w : List (Fin 3)) (C : Prop)
    (h : ∀ e : Fin 2, wordEnd (base e) w = base e → (wordPath (base e) w).Nodup → C)
    (x : Vertex) (hx : wordEnd x w = x) (hnd : (wordPath x w).Nodup) : C := by
  rw [eq_translateVertex_base x, wordEnd_translateVertex, (translateVertex_injective _).eq_iff]
    at hx
  rw [eq_translateVertex_base x, wordPath_translateVertex,
    List.nodup_map_iff (translateVertex_injective _)] at hnd
  exact h x.2 hx hnd

theorem four_word_base : ∀ (e : Fin 2) (a₁ a₂ a₃ a₄ : Fin 3),
    wordEnd (base e) [a₁, a₂, a₃, a₄] = base e →
      (wordPath (base e) [a₁, a₂, a₃, a₄]).Nodup → False := by
  decide

theorem four_word (x : Vertex) (a₁ a₂ a₃ a₄ : Fin 3) (hx : wordEnd x [a₁, a₂, a₃, a₄] = x)
    (hnd : (wordPath x [a₁, a₂, a₃, a₄]).Nodup) : False :=
  of_base _ False (fun e => four_word_base e a₁ a₂ a₃ a₄) x hx hnd

theorem six_word_base : ∀ (e : Fin 2) (a₁ a₂ a₃ a₄ a₅ a₆ : Fin 3),
    wordEnd (base e) [a₁, a₂, a₃, a₄, a₅, a₆] = base e →
      (wordPath (base e) [a₁, a₂, a₃, a₄, a₅, a₆]).Nodup →
        a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧ a₁ ≠ a₃ ∧ a₄ = a₁ ∧ a₅ = a₂ ∧ a₆ = a₃ := by
  decide

theorem six_word (x : Vertex) (a₁ a₂ a₃ a₄ a₅ a₆ : Fin 3)
    (hx : wordEnd x [a₁, a₂, a₃, a₄, a₅, a₆] = x)
    (hnd : (wordPath x [a₁, a₂, a₃, a₄, a₅, a₆]).Nodup) :
    a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧ a₁ ≠ a₃ ∧ a₄ = a₁ ∧ a₅ = a₂ ∧ a₆ = a₃ :=
  of_base _ _ (fun e => six_word_base e a₁ a₂ a₃ a₄ a₅ a₆) x hx hnd

theorem six_cycle_word_base : ∀ (e : Fin 2) (i j k : Fin 3), i ≠ j → j ≠ k → i ≠ k →
    wordEnd (base e) [i, j, k, i, j, k] = base e ∧
      (wordPath (base e) [i, j, k, i, j, k]).Nodup := by
  decide

theorem six_cycle_word (x : Vertex) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    wordEnd x [i, j, k, i, j, k] = x ∧ (wordPath x [i, j, k, i, j, k]).Nodup := by
  obtain ⟨h1, h2⟩ := six_cycle_word_base x.2 i j k hij hjk hik
  refine ⟨?_, ?_⟩
  · rw [eq_translateVertex_base x, wordEnd_translateVertex, h1]
  · rw [eq_translateVertex_base x, wordPath_translateVertex,
      List.nodup_map_iff (translateVertex_injective _)]
    exact h2

theorem exists_colours_four {x : Vertex} (p : P4.Walk x x) (hlen : p.length = 4) :
    ∃ a₁ a₂ a₃ a₄ : Fin 3, wordEnd x [a₁, a₂, a₃, a₄] = x ∧
      p.support = x :: wordPath x [a₁, a₂, a₃, a₄] := by
  rcases p with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | ⟨h₄, _ | ⟨h₅, p⟩⟩⟩⟩⟩ <;>
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hlen <;> try omega
  obtain ⟨a₁, rfl⟩ := adj_iff.mp h₁
  obtain ⟨a₂, rfl⟩ := adj_iff.mp h₂
  obtain ⟨a₃, rfl⟩ := adj_iff.mp h₃
  obtain ⟨a₄, ha₄⟩ := adj_iff.mp h₄
  refine ⟨a₁, a₂, a₃, a₄, ha₄.symm, ?_⟩
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, wordPath]
  rw [← ha₄]

theorem exists_colours_six {x : Vertex} (p : P4.Walk x x) (hlen : p.length = 6) :
    ∃ a₁ a₂ a₃ a₄ a₅ a₆ : Fin 3, wordEnd x [a₁, a₂, a₃, a₄, a₅, a₆] = x ∧
      p.support = x :: wordPath x [a₁, a₂, a₃, a₄, a₅, a₆] ∧ p.getVert 1 = nbr x a₁ ∧
      p.getVert 2 = nbr (nbr x a₁) a₂ ∧
      ∀ n < 6, colourAdj ([a₁, a₂, a₃, a₄, a₅, a₆].getD n 0) (p.getVert n) (p.getVert (n + 1)) := by
  rcases p with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | ⟨h₄, _ | ⟨h₅, _ | ⟨h₆, _ | ⟨h₇, p⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hlen <;> try omega
  obtain ⟨a₁, rfl⟩ := adj_iff.mp h₁
  obtain ⟨a₂, rfl⟩ := adj_iff.mp h₂
  obtain ⟨a₃, rfl⟩ := adj_iff.mp h₃
  obtain ⟨a₄, rfl⟩ := adj_iff.mp h₄
  obtain ⟨a₅, rfl⟩ := adj_iff.mp h₅
  obtain ⟨a₆, ha₆⟩ := adj_iff.mp h₆
  refine ⟨a₁, a₂, a₃, a₄, a₅, a₆, ha₆.symm, ?_, rfl, rfl, ?_⟩
  · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, wordPath]
    rw [← ha₆]
  · intro n hn
    interval_cases n
    · exact (colourAdj_iff_eq_nbr _ _ _).mpr rfl
    · exact (colourAdj_iff_eq_nbr _ _ _).mpr rfl
    · exact (colourAdj_iff_eq_nbr _ _ _).mpr rfl
    · exact (colourAdj_iff_eq_nbr _ _ _).mpr rfl
    · exact (colourAdj_iff_eq_nbr _ _ _).mpr rfl
    · exact (colourAdj_iff_eq_nbr _ _ _).mpr ha₆

theorem isCycle_cons_six {V : Type*} {G : SimpleGraph V} {v₀ v₁ v₂ v₃ v₄ v₅ : V}
    (h₁ : G.Adj v₀ v₁) (h₂ : G.Adj v₁ v₂) (h₃ : G.Adj v₂ v₃) (h₄ : G.Adj v₃ v₄)
    (h₅ : G.Adj v₄ v₅) (h₆ : G.Adj v₅ v₀) (hnd : [v₁, v₂, v₃, v₄, v₅, v₀].Nodup) :
    (SimpleGraph.Walk.cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅
      (.cons h₆ .nil)))))).IsCycle := by
  rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  refine ⟨hnd, fun h => ?_⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n12, n13, n14, n15, n10⟩, ⟨n23, n24, n25, n20⟩, ⟨n34, n35, n30⟩, ⟨n45, n40⟩, n50, -⟩ :=
    hnd
  simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h <;> rcases Sym2.eq_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  all_goals first
    | exact n12 hb | exact n20 ha.symm | exact n30 ha.symm | exact n13 hb | exact n40 ha.symm
    | exact n50 ha.symm | exact n15 hb

theorem exists_normalized_cycle {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    {q : G.Walk u u} (hq : q.IsCycle) {x y z : V} (hxz : x ≠ z) (hxy : s(x, y) ∈ q.edges)
    (hyz : s(y, z) ∈ q.edges) :
    ∃ q' : G.Walk x x, q'.IsCycle ∧ q'.length = q.length ∧
      q'.edges.toFinset = q.edges.toFinset ∧ q'.getVert 1 = y ∧ q'.getVert 2 = z := by
  have hx : x ∈ q.support := q.fst_mem_support_of_mem_edges hxy
  have hrc : (q.rotate x hx).IsCycle := hq.rotate hx
  have hredges : ∀ e, e ∈ (q.rotate x hx).edges ↔ e ∈ q.edges := fun e =>
    (q.rotate_edges x hx).perm.mem_iff
  have hnbr : ∀ {w : V} (r : G.Walk w w) (a b : V), s(a, b) ∈ r.edges →
      b ∈ r.toSubgraph.neighborSet a := fun r a b h => by
    rw [SimpleGraph.Subgraph.mem_neighborSet, ← SimpleGraph.Subgraph.mem_edgeSet,
      SimpleGraph.Walk.mem_edges_toSubgraph]
    exact h
  have hy := hnbr _ x y ((hredges _).mpr hxy)
  rw [hrc.neighborSet_toSubgraph_endpoint, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  obtain ⟨q', hq'c, hq'len, hq'edges, hq'1⟩ : ∃ q' : G.Walk x x, q'.IsCycle ∧
      q'.length = q.length ∧ (∀ e, e ∈ q'.edges ↔ e ∈ q.edges) ∧ q'.getVert 1 = y := by
    rcases hy with h | h
    · exact ⟨q.rotate x hx, hrc, SimpleGraph.Walk.length_rotate _ _ _, hredges, h.symm⟩
    · refine ⟨(q.rotate x hx).reverse, hrc.reverse, ?_, fun e => ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_rotate]
      · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse, hredges]
      · change (q.rotate x hx).reverse.snd = y
        rw [SimpleGraph.Walk.snd_reverse, h]
  have h3 := hq.three_le_length
  have hz := hnbr q' y z ((hq'edges _).mpr hyz)
  rw [← hq'1, hq'c.neighborSet_toSubgraph_internal (by norm_num) (by omega),
    Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h | h
  · exact absurd (h.trans (SimpleGraph.Walk.getVert_zero _)) (Ne.symm hxz)
  · refine ⟨q', hq'c, hq'len, ?_, hq'1, h.symm⟩
    ext e
    rw [List.mem_toFinset, List.mem_toFinset, hq'edges]

theorem card_vertex : Fintype.card Vertex = 32 := by
  rfl

theorem neighborFinset_eq (p : Vertex) : P4.neighborFinset p = Finset.univ.image (nbr p) := by
  ext q
  simp only [SimpleGraph.mem_neighborFinset, adj_iff, Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr fun i => eq_comm

theorem isRegularOfDegree : P4.IsRegularOfDegree 3 := by
  intro p
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_eq,
    Finset.card_image_of_injective _ fun i j h => nbr_injective p i j h]
  rfl

@[expose] def parity : P4.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun p => decide (p.2 = 1)) fun {p q} h => by
    obtain ⟨i, rfl⟩ := adj_iff.mp h
    revert p i
    decide

theorem isBipartite : P4.IsBipartite := by
  simpa using parity.colorable

theorem nbr_nbr_shift : ∀ v : ZMod 4 × ZMod 4,
    nbr (nbr (v, 0) 1) 0 = ((v.1 + 1, v.2), 0) ∧ nbr (nbr (v, 0) 2) 0 = ((v.1, v.2 + 1), 0) := by
  decide

theorem connected : P4.Connected := by
  have hadj : ∀ (p : Vertex) (i : Fin 3), P4.Reachable p (nbr p i) := fun p i =>
    (adj_nbr p i).reachable
  have h1 : ∀ v : ZMod 4 × ZMod 4, P4.Reachable (v, 0) ((v.1 + 1, v.2), 0) := fun v => by
    rw [← (nbr_nbr_shift v).1]
    exact (hadj _ 1).trans (hadj _ 0)
  have h2 : ∀ v : ZMod 4 × ZMod 4, P4.Reachable (v, 0) ((v.1, v.2 + 1), 0) := fun v => by
    rw [← (nbr_nbr_shift v).2]
    exact (hadj _ 2).trans (hadj _ 0)
  have hA : ∀ n : ℕ, P4.Reachable o (((n : ZMod 4), 0), 0) := by
    intro n
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      have h := h1 ((n : ZMod 4), 0)
      rw [← Nat.cast_succ] at h
      exact ih.trans h
  have hB : ∀ (a : ZMod 4) (n : ℕ), P4.Reachable ((a, 0), 0) ((a, (n : ZMod 4)), 0) := by
    intro a n
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      have h := h2 (a, (n : ZMod 4))
      rw [← Nat.cast_succ] at h
      exact ih.trans h
  have heven : ∀ v : ZMod 4 × ZMod 4, P4.Reachable o (v, 0) := fun v => by
    have h := (hA v.1.val).trans (hB _ v.2.val)
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
  refine ⟨fun p q => ?_⟩
  have hall : ∀ p : Vertex, P4.Reachable o p := by
    rintro ⟨v, e⟩
    fin_cases e
    · exact heven v
    · have h := (heven v).trans (hadj (v, 0) 0)
      have hv : nbr (v, 0) 0 = (v, 1) := by
        change (v + s 0, 1) = (v, 1)
        rw [show s 0 = 0 from rfl, add_zero]
      rwa [hv] at h
  exact (hall p).symm.trans (hall q)

end CFSG.Combinatorics.FourByFourPeriodicGraph

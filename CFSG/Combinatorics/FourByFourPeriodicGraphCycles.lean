module

public import CFSG.Combinatorics.FourByFourPeriodicGraphSupport
public import CFSG.Combinatorics.UniqueCycleFaithful
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Girth

public section

namespace CFSG.Combinatorics.FourByFourPeriodicGraph

theorem exists_six_cycle (x : Vertex) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ W : P4.Walk x x, W.IsCycle ∧ W.length = 6 ∧
      W.support = x :: wordPath x [i, j, k, i, j, k] ∧ W.getVert 1 = nbr x i ∧
      W.getVert 2 = nbr (nbr x i) j ∧ s(x, nbr x i) ∈ W.edges ∧
      s(nbr x i, nbr (nbr x i) j) ∈ W.edges := by
  obtain ⟨hend, hnd⟩ := six_cycle_word x hij hjk hik
  have hend' : nbr (nbr (nbr (nbr (nbr (nbr x i) j) k) i) j) k = x := hend
  have h₆ : P4.Adj (nbr (nbr (nbr (nbr (nbr x i) j) k) i) j) x := by
    have h := adj_nbr (nbr (nbr (nbr (nbr (nbr x i) j) k) i) j) k
    rwa [hend'] at h
  have hnd' : [nbr x i, nbr (nbr x i) j, nbr (nbr (nbr x i) j) k,
      nbr (nbr (nbr (nbr x i) j) k) i, nbr (nbr (nbr (nbr (nbr x i) j) k) i) j, x].Nodup := by
    have h : wordPath x [i, j, k, i, j, k] = [nbr x i, nbr (nbr x i) j,
        nbr (nbr (nbr x i) j) k, nbr (nbr (nbr (nbr x i) j) k) i,
        nbr (nbr (nbr (nbr (nbr x i) j) k) i) j,
        nbr (nbr (nbr (nbr (nbr (nbr x i) j) k) i) j) k] := rfl
    rw [h, hend'] at hnd
    exact hnd
  refine ⟨.cons (adj_nbr x i) (.cons (adj_nbr _ j) (.cons (adj_nbr _ k) (.cons (adj_nbr _ i)
    (.cons (adj_nbr _ j) (.cons h₆ .nil))))), isCycle_cons_six _ _ _ _ _ h₆ hnd', rfl, ?_, rfl,
    rfl, ?_, ?_⟩
  · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, wordPath]
    rw [hend']
  · simp [SimpleGraph.Walk.edges_cons]
  · simp [SimpleGraph.Walk.edges_cons]

theorem six_le_length_of_isCycle {u : Vertex} (p : P4.Walk u u) (hp : p.IsCycle) :
    6 ≤ p.length := by
  have heven : Even p.length := (parity.even_length_iff_congr p).mpr Iff.rfl
  have h3 := hp.three_le_length
  by_contra hlt
  have h4 : p.length = 4 := by
    obtain ⟨m, hm⟩ := heven
    omega
  obtain ⟨a₁, a₂, a₃, a₄, hend, hsupp⟩ := exists_colours_four p h4
  have hnd := hp.support_nodup
  rw [hsupp, List.tail_cons] at hnd
  exact four_word u a₁ a₂ a₃ a₄ hend hnd

theorem eq_of_ne_of_ne : ∀ a b c d : Fin 3, a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c = d := by
  decide

theorem support_eq_of_six_cycle {x : Vertex} {p : P4.Walk x x} (hpc : p.IsCycle)
    (hplen : p.length = 6) {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (hp1 : p.getVert 1 = nbr x i) (hp2 : p.getVert 2 = nbr (nbr x i) j) :
    p.support = x :: wordPath x [i, j, k, i, j, k] ∧
      ∀ n < 6, colourAdj ([i, j, k, i, j, k].getD n 0) (p.getVert n) (p.getVert (n + 1)) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, hend, hsupp, hv1, hv2, hcol⟩ := exists_colours_six p hplen
  have hnd := hpc.support_nodup
  rw [hsupp, List.tail_cons] at hnd
  obtain ⟨h12, h23, h13, h41, h52, h63⟩ := six_word x a₁ a₂ a₃ a₄ a₅ a₆ hend hnd
  have ha₁ : a₁ = i := nbr_injective x a₁ i (hv1.symm.trans hp1)
  subst ha₁
  have ha₂ : a₂ = j := nbr_injective _ a₂ j (hv2.symm.trans hp2)
  subst ha₂
  have ha₃ : a₃ = k := eq_of_ne_of_ne a₁ a₂ a₃ k h12 (Ne.symm h13) (Ne.symm h23) hki hkj
  subst ha₃
  rw [h41, h52, h63] at hsupp hcol
  exact ⟨hsupp, hcol⟩

theorem existsUnique_six_cycle {x y z : Vertex} (hxz : x ≠ z) (hxy : P4.Adj x y)
    (hyz : P4.Adj y z) :
    ∃! p : P4.Walk x x, p.IsCycle ∧ p.length = 6 ∧ p.getVert 1 = y ∧ p.getVert 2 = z := by
  obtain ⟨i, rfl⟩ := adj_iff.mp hxy
  obtain ⟨j, rfl⟩ := adj_iff.mp hyz
  have hij : i ≠ j := by
    rintro rfl
    exact hxz (nbr_nbr x i).symm
  obtain ⟨k, hki, hkj⟩ := (by decide : ∀ a b : Fin 3, a ≠ b → ∃ c, c ≠ a ∧ c ≠ b) i j hij
  obtain ⟨W, hWc, hWlen, hWsupp, hW1, hW2, -, -⟩ := exists_six_cycle x hij hkj.symm hki.symm
  refine ⟨W, ⟨hWc, hWlen, hW1, hW2⟩, ?_⟩
  rintro p ⟨hpc, hplen, hp1, hp2⟩
  exact SimpleGraph.Walk.ext_support
    ((support_eq_of_six_cycle hpc hplen hki hkj hp1 hp2).1.trans hWsupp.symm)

theorem existsUnique_six_cycle_edgeSet {x y z : Vertex} (hxz : x ≠ z) (hxy : P4.Adj x y)
    (hyz : P4.Adj y z) :
    ∃! s : Finset (Sym2 Vertex), (∃ (u : Vertex) (p : P4.Walk u u), p.IsCycle ∧
      p.length = 6 ∧ p.edges.toFinset = s) ∧ s(x, y) ∈ s ∧ s(y, z) ∈ s := by
  obtain ⟨W, ⟨hWc, hWlen, hW1, hW2⟩, hWuniq⟩ := existsUnique_six_cycle hxz hxy hyz
  obtain ⟨i, rfl⟩ := adj_iff.mp hxy
  obtain ⟨j, rfl⟩ := adj_iff.mp hyz
  have hij : i ≠ j := by
    rintro rfl
    exact hxz (nbr_nbr x i).symm
  obtain ⟨k, hki, hkj⟩ := (by decide : ∀ a b : Fin 3, a ≠ b → ∃ c, c ≠ a ∧ c ≠ b) i j hij
  obtain ⟨W', hW'c, hW'len, -, hW'1, hW'2, hW'xy, hW'yz⟩ :=
    exists_six_cycle x hij hkj.symm hki.symm
  have hW'W : W' = W := hWuniq W' ⟨hW'c, hW'len, hW'1, hW'2⟩
  refine ⟨W'.edges.toFinset, ⟨⟨x, W', hW'c, hW'len, rfl⟩, List.mem_toFinset.mpr hW'xy,
    List.mem_toFinset.mpr hW'yz⟩, ?_⟩
  rintro _ ⟨⟨u, q, hqc, hqlen, rfl⟩, hsxy, hsyz⟩
  obtain ⟨q', hq'c, hq'len, hq'edges, hq'1, hq'2⟩ := exists_normalized_cycle hqc hxz
    (List.mem_toFinset.mp hsxy) (List.mem_toFinset.mp hsyz)
  have hq'W : q' = W := hWuniq q' ⟨hq'c, hq'len.trans hqlen, hq'1, hq'2⟩
  rw [← hq'edges, hq'W, hW'W]

theorem four_by_four_periodic_cubic_graph_local_cycles_and_automorphism_bound :
    P4.Connected ∧ P4.IsBipartite ∧ P4.IsRegularOfDegree 3 ∧ Fintype.card Vertex = 32 ∧
    (∀ (u : Vertex) (p : P4.Walk u u), p.IsCycle → 6 ≤ p.length) ∧
    (∃ (u : Vertex) (p : P4.Walk u u), p.IsCycle ∧ p.length = 6) ∧ P4.girth = 6 ∧
    (∀ x y z : Vertex, x ≠ z → P4.Adj x y → P4.Adj y z →
      ∃! p : P4.Walk x x, p.IsCycle ∧ p.length = 6 ∧ p.getVert 1 = y ∧ p.getVert 2 = z) ∧
    (∀ x y z : Vertex, x ≠ z → P4.Adj x y → P4.Adj y z →
      ∃! s : Finset (Sym2 Vertex), (∃ (u : Vertex) (p : P4.Walk u u), p.IsCycle ∧
        p.length = 6 ∧ p.edges.toFinset = s) ∧ s(x, y) ∈ s ∧ s(y, z) ∈ s) ∧
    (∀ (x y z : Vertex) (i j k : Fin 3), i ≠ j → j ≠ k → i ≠ k → colourAdj i x y →
      colourAdj j y z → ∀ p : P4.Walk x x, p.IsCycle → p.length = 6 → p.getVert 1 = y →
        p.getVert 2 = z → ∀ n : Fin 6,
          colourAdj (![i, j, k, i, j, k] n) (p.getVert n) (p.getVert ((n : ℕ) + 1))) ∧
    (∀ (u : Vertex) (p : P4.Walk u u), p.IsCycle → p.length = 6 → ∃ i j k : Fin 3,
      i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ ∀ n : Fin 6,
        colourAdj (![i, j, k, i, j, k] n) (p.getVert n) (p.getVert ((n : ℕ) + 1))) ∧
    Nat.card (P4 ≃g P4) ≤ 192 := by
  obtain ⟨W₀, hW₀c, hW₀len, -⟩ := exists_six_cycle o (i := 0) (j := 1) (k := 2) (by decide)
    (by decide) (by decide)
  have hvec : ∀ (i j k : Fin 3) (n : Fin 6),
      ![i, j, k, i, j, k] n = [i, j, k, i, j, k].getD n 0 := by
    intro i j k n
    fin_cases n <;> rfl
  refine ⟨connected, isBipartite, isRegularOfDegree, card_vertex,
    fun u p hp => six_le_length_of_isCycle p hp, ⟨o, W₀, hW₀c, hW₀len⟩, ?_,
    fun x y z hxz hxy hyz => existsUnique_six_cycle hxz hxy hyz,
    fun x y z hxz hxy hyz => existsUnique_six_cycle_edgeSet hxz hxy hyz, ?_, ?_, ?_⟩
  ·
    have hacyc : ¬ P4.IsAcyclic := fun h => h W₀ hW₀c
    obtain ⟨a, w, hw, hgw⟩ := SimpleGraph.exists_girth_eq_length.mpr hacyc
    have h1 := six_le_length_of_isCycle w hw
    have h2 := hW₀c.girth_le_length
    omega
  ·
    intro x y z i j k hij hjk hik hi hj p hpc hplen hp1 hp2 n
    rw [colourAdj_iff_eq_nbr] at hi hj
    subst hi hj
    rw [hvec]
    exact (support_eq_of_six_cycle hpc hplen hik.symm hjk.symm hp1 hp2).2 n n.2
  ·
    intro u p hpc hplen
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, hend, hsupp, -, -, hcol⟩ := exists_colours_six p hplen
    have hnd := hpc.support_nodup
    rw [hsupp, List.tail_cons] at hnd
    obtain ⟨h12, h23, h13, h41, h52, h63⟩ := six_word u a₁ a₂ a₃ a₄ a₅ a₆ hend hnd
    rw [h41, h52, h63] at hcol
    refine ⟨a₁, a₂, a₃, h12, h23, h13, fun n => ?_⟩
    rw [hvec]
    exact hcol n n.2
  ·
    have h := (UniqueCycleFaithful.unique_fixed_length_cycles_make_neighborhood_action_faithful
      P4 connected 3 isRegularOfDegree (by norm_num) 6 (by norm_num)
      fun x y z hxz hxy hyz => existsUnique_six_cycle_edgeSet hxz hxy hyz).2
    rw [card_vertex] at h
    exact h

end CFSG.Combinatorics.FourByFourPeriodicGraph

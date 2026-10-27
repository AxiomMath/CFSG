module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Tree

variable {V : Type*} {T : SimpleGraph V}

private lemma dist_add_dist_le_length {s t x : V} (P : T.Walk s t) (hx : x ∈ P.support) :
    T.dist s x + T.dist x t ≤ P.length := by
  classical
  have hsplit := congrArg SimpleGraph.Walk.length (P.take_spec hx)
  rw [SimpleGraph.Walk.length_append] at hsplit
  have h1 := SimpleGraph.dist_le (P.takeUntil x hx)
  have h2 := SimpleGraph.dist_le (P.dropUntil x hx)
  omega

private lemma eq_of_key (hT : T.IsTree) {u v a b : V} (huv : T.Adj u v) (hab : T.Adj a b)
    (h1 : T.dist a v = T.dist a u + 1) (h2 : T.dist b u = T.dist b v + 1)
    (h3 : T.dist a u = T.dist b v) : a = u ∧ b = v := by
  have c1 : T.dist u a = T.dist a u := SimpleGraph.dist_comm
  have c2 : T.dist v a = T.dist a v := SimpleGraph.dist_comm
  have c3 : T.dist v b = T.dist b v := SimpleGraph.dist_comm
  have c4 : T.dist u b = T.dist b u := SimpleGraph.dist_comm
  obtain ⟨R, hR, hRlen⟩ := hT.connected.exists_path_of_dist u a
  have hvR : v ∉ R.support := by
    intro hv
    have := dist_add_dist_le_length R hv
    omega
  have hY : (SimpleGraph.Walk.cons huv.symm R).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hR, hvR⟩
  obtain ⟨S, hS, hSlen⟩ := hT.connected.exists_path_of_dist v b
  have haS : a ∉ S.support := by
    intro ha
    have := dist_add_dist_le_length S ha
    omega
  have hZ : (S.concat hab.symm).IsPath := hS.concat haS hab.symm
  have hYZ := (hT.existsUnique_path v a).unique hY hZ
  have huY : u ∈ (SimpleGraph.Walk.cons huv.symm R).support := by
    rw [SimpleGraph.Walk.support_cons]
    exact List.mem_cons_of_mem _ R.start_mem_support
  rw [hYZ] at huY
  simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at huY
  rcases huY with huS | hua
  · have := dist_add_dist_le_length S huS
    omega
  · have hk : T.dist a u = 0 := by rw [hua, SimpleGraph.dist_self]
    have hbv : T.dist b v = 0 := by omega
    exact ⟨hua.symm, hT.connected.dist_eq_zero_iff.mp hbv⟩

theorem dist_adj (hT : T.IsTree) {a b : V} (hab : T.Adj a b) (w : V) :
    T.dist w b = T.dist w a + 1 ∨ T.dist w a = T.dist w b + 1 :=
  hT.dist_eq_dist_add_one_of_adj w hab.symm

theorem eq_of_dist_sum_eq (hT : T.IsTree) {u v a b : V} (huv : T.Adj u v) (hab : T.Adj a b)
    (h : T.dist a u + T.dist a v = T.dist b u + T.dist b v) :
    (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  have h1 := dist_adj hT huv a
  have h2 := dist_adj hT huv b
  have h3 := dist_adj hT hab u
  have c1 : T.dist u b = T.dist b u := SimpleGraph.dist_comm
  have c2 : T.dist u a = T.dist a u := SimpleGraph.dist_comm
  rcases (show (T.dist a v = T.dist a u + 1 ∧ T.dist b u = T.dist b v + 1 ∧
      T.dist a u = T.dist b v) ∨
      (T.dist b v = T.dist b u + 1 ∧ T.dist a u = T.dist a v + 1 ∧
      T.dist b u = T.dist a v) by omega) with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · exact Or.inl (eq_of_key hT huv hab e1 e2 e3)
  · obtain ⟨hbu, hav⟩ := eq_of_key hT huv hab.symm e1 e2 e3
    exact Or.inr ⟨hav, hbu⟩

theorem dist_perm_eq {σ : Equiv.Perm V} (hσ : ∀ u v, T.Adj (σ u) (σ v) ↔ T.Adj u v) (u v : V) :
    T.dist (σ u) (σ v) = T.dist u v := by
  have hle : ∀ τ : Equiv.Perm V, (∀ x y, T.Adj (τ x) (τ y) ↔ T.Adj x y) →
      ∀ x y, T.Reachable x y → T.dist (τ x) (τ y) ≤ T.dist x y := by
    intro τ hτ x y hxy
    obtain ⟨p, hp⟩ := hxy.exists_walk_length_eq_dist
    have hmap := SimpleGraph.dist_le (p.map (⟨⇑τ, fun {a b} h => (hτ a b).mpr h⟩ : T →g T))
    rw [SimpleGraph.Walk.length_map, hp] at hmap
    exact hmap
  have hσ' : ∀ x y, T.Adj (σ.symm x) (σ.symm y) ↔ T.Adj x y := by
    intro x y
    have h := hσ (σ.symm x) (σ.symm y)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  have hreach : ∀ x y, T.Reachable x y ↔ T.Reachable (σ x) (σ y) := by
    intro x y
    refine ⟨fun h => h.map (⟨⇑σ, fun {a b} h' => (hσ a b).mpr h'⟩ : T →g T), fun h => ?_⟩
    have h' : T.Reachable (σ.symm (σ x)) (σ.symm (σ y)) :=
      h.map (⟨⇑σ.symm, fun {a b} h'' => (hσ' a b).mpr h''⟩ : T →g T)
    rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h'
  by_cases hr : T.Reachable u v
  · refine le_antisymm (hle σ hσ u v hr) ?_
    have h' := hle σ.symm hσ' (σ u) (σ v) ((hreach u v).mp hr)
    rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h'
  · have hr' : ¬ T.Reachable (σ u) (σ v) := fun h => hr ((hreach u v).mpr h)
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hr,
      SimpleGraph.dist_eq_zero_of_not_reachable hr']

end CFSG.AGLEmbeddingD2.Tits.GN516.Tree

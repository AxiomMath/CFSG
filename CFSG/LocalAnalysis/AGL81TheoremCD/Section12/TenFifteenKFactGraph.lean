module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.UniqueBranch
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.NoBranch
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.TripleEdge
public import CFSG.LieType.RootSystem.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbTreeDist

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

section Tree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem card_degree_eq_one_le_three (hG : G.IsTree) (hdeg : ∀ v, G.degree v ≤ 3)
    (hbranch : ∀ u v, G.degree u = 3 → G.degree v = 3 → u = v) :
    (Finset.univ.filter fun v => G.degree v = 1).card ≤ 3 := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hcard := hG.card_edgeFinset
  have h3 : (Finset.univ.filter fun v => G.degree v = 3).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb =>
      hbranch a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  have hle : ∑ v, (G.degree v + if G.degree v = 1 then 1 else 0) ≤
      ∑ v, (2 + if G.degree v = 3 then 1 else 0) := by
    refine Finset.sum_le_sum fun v _ => ?_
    have := hdeg v
    split_ifs <;> omega
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.card_filter, ← Finset.card_filter,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, hsum] at hle
  omega

omit [DecidableEq V] in
theorem degree_perm_eq {σ : Equiv.Perm V} (hσ : ∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v) (v : V) :
    G.degree (σ v) = G.degree v :=
  SimpleGraph.Iso.degree_eq (G := G) (G' := G) ⟨σ, fun {a b} => hσ a b⟩ v

omit [Fintype V] [DecidableRel G.Adj] in
theorem eq_of_adj_of_dist_add_one_eq (hG : G.IsTree) (r : V) {c v w : V} (hv : G.Adj c v)
    (hw : G.Adj c w) (hvd : G.dist r v + 1 = G.dist r c) (hwd : G.dist r w + 1 = G.dist r c) :
    v = w := by
  obtain ⟨R, hR, hRlen⟩ := hG.connected.exists_path_of_dist r v
  obtain ⟨S, hS, hSlen⟩ := hG.connected.exists_path_of_dist r w
  have hcR : c ∉ R.support := fun hc => by
    have h1 := SimpleGraph.dist_le (R.takeUntil c hc)
    have h2 := R.length_takeUntil_le hc
    omega
  have hcS : c ∉ S.support := fun hc => by
    have h1 := SimpleGraph.dist_le (S.takeUntil c hc)
    have h2 := S.length_takeUntil_le hc
    omega
  have hYZ := (hG.existsUnique_path r c).unique (hR.concat hcR hv.symm) (hS.concat hcS hw.symm)
  have h := congrArg SimpleGraph.Walk.penultimate hYZ
  rwa [SimpleGraph.Walk.penultimate_concat, SimpleGraph.Walk.penultimate_concat] at h

theorem eq_one_of_forall_degree_eq_one (hG : G.IsTree) {σ : Equiv.Perm V}
    (hσ : ∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v) (hfix : ∀ v, G.degree v = 1 → σ v = v) :
    σ = 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Equiv.ext fun v => Subsingleton.elim _ _
  obtain ⟨r, hr⟩ := hG.exists_vert_degree_one_of_nontrivial
  have hσr : σ r = r := hfix r hr
  by_contra hne
  obtain ⟨v₀, hv₀⟩ : ∃ v, σ v ≠ v := by
    by_contra hcon
    exact hne (Equiv.ext fun v => by_contra fun h => hcon ⟨v, h⟩)
  obtain ⟨v, hvM, hvmax⟩ := Finset.exists_max_image (Finset.univ.filter fun v => σ v ≠ v)
    (fun v => G.dist r v) ⟨v₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv₀⟩⟩
  have hσv : σ v ≠ v := (Finset.mem_filter.1 hvM).2
  have hdeg : 1 < (G.neighborFinset v).card := by
    have hpos := hG.connected.preconnected.degree_pos_of_nontrivial v
    have h1 : G.degree v ≠ 1 := fun h => hσv (hfix v h)
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hdeg
  rw [SimpleGraph.mem_neighborFinset] at hx hy
  obtain ⟨c, hc, hcd⟩ : ∃ c, G.Adj v c ∧ G.dist r c = G.dist r v + 1 := by
    rcases CFSG.AGLEmbeddingD2.Tits.GN516.Tree.dist_adj hG hx r with h1 | h1
    · exact ⟨x, hx, h1⟩
    rcases CFSG.AGLEmbeddingD2.Tits.GN516.Tree.dist_adj hG hy r with h2 | h2
    · exact ⟨y, hy, h2⟩
    exact absurd (eq_of_adj_of_dist_add_one_eq hG r hx hy h1.symm h2.symm) hxy
  have hσc : σ c = c := by
    by_contra hcne
    have := hvmax c (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcne⟩)
    omega
  have h1 : G.Adj c (σ v) := by
    have h := (hσ v c).2 hc
    rw [hσc] at h
    exact h.symm
  have h2 : G.dist r (σ v) + 1 = G.dist r c := by
    have h := CFSG.AGLEmbeddingD2.Tits.GN516.Tree.dist_perm_eq hσ r v
    rw [hσr] at h
    omega
  exact hσv (eq_of_adj_of_dist_add_one_eq hG r h1 hc.symm h2 hcd.symm)

omit [Fintype V] in
theorem apply_eq_self_of_card_le_three {σ : Equiv.Perm V} {L : Finset V}
    (hL : ∀ v ∈ L, σ v ∈ L) (hcard : L.card ≤ 3) {m : ℕ} (hm : Nat.Coprime m 6)
    (hσm : σ ^ m = 1) {v : V} (hv : v ∈ L) : σ v = v := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hm
  have hper : Function.IsPeriodicPt σ m v := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow, hσm,
      Equiv.Perm.one_apply]
  have hmem : ∀ k : ℕ, σ^[k] v ∈ L := fun k => by
    induction k with
    | zero => exact hv
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hL _ ih
  have hk : Function.minimalPeriod σ v ≤ 3 := by
    have hinj : Set.InjOn (fun k => σ^[k] v)
        ((Finset.range (Function.minimalPeriod σ v) : Finset ℕ) : Set ℕ) := by
      rw [Finset.coe_range]
      exact Function.iterate_injOn_Iio_minimalPeriod
    have hsub : (Finset.range (Function.minimalPeriod σ v)).image (fun k => σ^[k] v) ⊆ L := by
      intro w hw
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hw
      exact hmem k
    have h := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_range] at h
    omega
  have hkpos := hper.minimalPeriod_pos hm0
  have hcop := Nat.Coprime.coprime_dvd_left hper.minimalPeriod_dvd hm
  have h1 : Function.minimalPeriod σ v = 1 := by
    generalize Function.minimalPeriod σ v = k at hk hkpos hcop ⊢
    interval_cases k
    · rfl
    all_goals exact absurd hcop (by decide)
  exact Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1

theorem eq_one_of_pow_eq_one_of_isTree (hG : G.IsTree) (hdeg : ∀ v, G.degree v ≤ 3)
    (hbranch : ∀ u v, G.degree u = 3 → G.degree v = 3 → u = v) {σ : Equiv.Perm V}
    (hσ : ∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v) {m : ℕ} (hm : Nat.Coprime m 6)
    (hσm : σ ^ m = 1) : σ = 1 := by
  refine eq_one_of_forall_degree_eq_one hG hσ fun v hv => ?_
  refine apply_eq_self_of_card_le_three (L := Finset.univ.filter fun v => G.degree v = 1)
    (fun u hu => ?_) (card_degree_eq_one_le_three hG hdeg hbranch) hm hσm ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [degree_perm_eq hσ]
    exact hu
  · simpa using hv

end Tree

section Diagram

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}

theorem eq_of_degree_eq_three_of_connected (hA : TauCeti.IsFiniteType A)
    (hconn : (TauCeti.diagramGraph A).Connected) {u v : ι}
    (hu : (TauCeti.diagramGraph A).degree u = 3) (hv : (TauCeti.diagramGraph A).degree v = 3) :
    u = v := by
  by_cases hsl : A.IsSimplyLaced
  · exact hA.eq_of_degree_eq_three hsl hconn hu hv
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, i ≠ j ∧ ¬ (A i j = 0 ∨ A i j = -1) := by
    by_contra hcon
    exact hsl fun i j hij => by_contra fun h => hcon ⟨i, j, hij, h⟩
  have hlt := (TauCeti.diagramGraph A).degree_lt_card_verts u
  rcases CFSG.LieType.RootSystem.cartan_pair_cases hA hij with
    ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (Or.inl h1) hne
  · exact absurd (Or.inr h1) hne
  · have := hA.degree_le_two_of_apply_mul_apply_eq_two hconn.preconnected
      (by rw [h1, h2]; norm_num : A i j * A j i = 2) u
    omega
  · have := hA.degree_le_two_of_apply_mul_apply_eq_two hconn.preconnected
      (by rw [h1, h2]; norm_num : A i j * A j i = 2) u
    omega
  all_goals
    have h3 : A i j * A j i = 3 := by rw [h1, h2]; norm_num
    have hle : Fintype.card ι ≤ 2 := by
      rw [← Finset.card_univ]
      refine (Finset.card_le_card fun k _ => ?_).trans (Finset.card_le_two (a := i) (b := j))
      rcases hA.eq_or_eq_of_apply_mul_apply_eq_three hconn.preconnected h3 k with rfl | rfl <;>
        simp
    omega

theorem eq_one_of_diagram_perm (hA : TauCeti.IsFiniteType A)
    (hconn : (TauCeti.diagramGraph A).Connected) {σ : Equiv.Perm ι}
    (hσ : ∀ i j, (TauCeti.diagramGraph A).Adj (σ i) (σ j) ↔ (TauCeti.diagramGraph A).Adj i j)
    {m : ℕ} (hm : Nat.Coprime m 6) (hσm : σ ^ m = 1) : σ = 1 :=
  eq_one_of_pow_eq_one_of_isTree (hA.isTree_diagramGraph hconn) hA.degree_le_three
    (fun _ _ hu hv => eq_of_degree_eq_three_of_connected hA hconn hu hv) hσ hm hσm

end Diagram

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

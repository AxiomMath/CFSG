module

public import CFSG.Combinatorics.AperiodicOppositeComponentsSigma

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem eq_of_mid (H : MooreHyp G) {a b x y : V} (hab : G.dist a b = 4)
    (hax : G.dist a x = 2) (hxb : G.dist x b = 2) (hay : G.dist a y = 2) (hyb : G.dist y b = 2) :
    x = y := by
  obtain ⟨nx, hxn, hbn⟩ := exists_adj_adj_of_dist_eq_two H.conn hxb
  obtain ⟨ny, hyn, hbn'⟩ := exists_adj_adj_of_dist_eq_two H.conn hyb
  have hdn : ∀ {t n : V}, G.dist a t = 2 → G.Adj t n → G.Adj b n → G.dist a n = 3 := by
    intro t n ht htn hbn
    have h1 := H.conn.dist_triangle (u := a) (v := t) (w := n)
    have h2 := H.conn.dist_triangle (u := a) (v := n) (w := b)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr htn] at h1
    rw [SimpleGraph.dist_comm (u := n), SimpleGraph.dist_eq_one_iff_adj.mpr hbn] at h2
    omega
  have hnn : nx = ny := pred_unique H.cyc H.conn (k := 3) (by norm_num)
    (show G.dist a b = 3 + 1 from hab) hbn hbn' (hdn hax hxn hbn) (hdn hay hyn hbn')
  subst hnn
  exact pred_unique H.cyc H.conn (k := 2) (by norm_num)
    (show G.dist a nx = 2 + 1 from hdn hax hxn hbn) hxn.symm hyn.symm hax hay

omit [Fintype V] [DecidableEq V] in
theorem exists_adj_adj_of_dist_two {W : Type*} {Γ : SimpleGraph W} {x y : W}
    (hr : Γ.Reachable x y) (h : Γ.dist x y = 2) : ∃ a, Γ.Adj x a ∧ Γ.Adj a y := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [h] at hp
  rcases p with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, p⟩⟩⟩ <;>
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hp <;> try omega
  exact ⟨_, h₁, h₂⟩

variable {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (F : IsFrame G col w ℓ p z q c ε)
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)
  (haper : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x)

include F in
theorem dist_eq_three_of_path {x₀ x₁ x₂ x₃ : {v : V // col v = false}}
    (h₀ : (pointGraph G col).dist w x₀ = 3) (h₁ : (pointGraph G col).dist w x₁ = 3)
    (h₂ : (pointGraph G col).dist w x₂ = 3) (h₃ : (pointGraph G col).dist w x₃ = 3)
    (a01 : (pointGraph G col).Adj x₀ x₁) (a12 : (pointGraph G col).Adj x₁ x₂)
    (a23 : (pointGraph G col).Adj x₂ x₃) (n02 : x₀ ≠ x₂) (n13 : x₁ ≠ x₃) :
    (pointGraph G col).dist x₀ x₃ = 3 := by
  have hd := point_dist_eq_iff F.moore.conn col
  have f : ∀ {x : {v : V // col v = false}}, (pointGraph G col).dist w x = 3 →
      G.dist (w : V) x = 6 := fun hx => (hd w _ 3).mp hx
  have hV : ∀ {a b : {v : V // col v = false}}, a ≠ b → (a : V) ≠ b :=
    fun h h' => h (Subtype.ext h')
  obtain ⟨m₀, -, x₀m₀, x₁m₀, -⟩ := F.edge h₀ h₁ a01
  obtain ⟨m₁, -, x₁m₁, x₂m₁, -⟩ := F.edge h₁ h₂ a12
  obtain ⟨m₂, -, x₂m₂, x₃m₂, -⟩ := F.edge h₂ h₃ a23
  have m01 : m₀ ≠ m₁ := fun h => not_three_far_on_line F.moore col (f h₀) (f h₁) (f h₂) x₀m₀
    x₁m₀ (by rw [h]; exact x₂m₁) (hV a01.ne) (hV n02) (hV a12.ne)
  have m12 : m₁ ≠ m₂ := fun h => not_three_far_on_line F.moore col (f h₁) (f h₂) (f h₃) x₁m₁
    x₂m₁ (by rw [h]; exact x₃m₂) (hV a12.ne) (hV n13) (hV a23.ne)
  obtain ⟨-, -, -, -, d⟩ := dist_of_path_six F.moore col x₀m₀ x₁m₀.symm x₁m₁ x₂m₁.symm x₂m₂
    x₃m₂.symm (hV a01.ne.symm) m01.symm (hV a12.ne.symm) m12.symm (hV a23.ne.symm)
  exact (hd x₀ x₃ 3).mpr d

include F hr in
theorem dist_three_of_word {x : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3)
    {a b d : Fin 3} (hab : a ≠ b) (hbd : b ≠ d) :
    (pointGraph G col).dist x (r d (r b (r a x))) = 3 := by
  obtain ⟨h₁, a01, c01⟩ := hr a x hx
  obtain ⟨h₂, a12, c12⟩ := hr b _ h₁
  obtain ⟨h₃, a23, c23⟩ := hr d _ h₂
  have hne : ∀ {u v t : {v : V // col v = false}}, c v u ≠ c v t → u ≠ t :=
    fun h e => h (by rw [e])
  have n02 : x ≠ r b (r a x) :=
    hne (v := r a x) (by rw [F.symm hx h₁ a01, c01, c12]; exact hab)
  have n13 : r a x ≠ r d (r b (r a x)) :=
    hne (v := r b (r a x)) (by rw [F.symm h₁ h₂ a12, c12, c23]; exact hbd)
  exact dist_eq_three_of_path F hx h₁ h₂ h₃ a01 a12 a23 n02 n13

include F hr haper in
theorem dist_sigmaMap {x : {v : V // col v = false}} (hx : x ∈ oppSet G col w) :
    (pointGraph G col).dist x (sigmaMap G col w x) = 3 := by
  obtain ⟨hσ, -, hiff⟩ := sigmaMap_dist F hr haper hx
  have h4 : (oppGraph G col w).dist ⟨x, hx⟩ ⟨sigmaMap G col w x, hσ⟩ = 4 := (hiff _ hσ).mpr rfl
  have hd := point_dist_eq_iff F.moore.conn col
  have hA := point_adj_iff F.moore.conn col
  have hle : (pointGraph G col).dist x (sigmaMap G col w x) ≤ 3 := by
    rw [(point_dist F.moore.conn col x _).1]
    have := dist_le_six F.moore.cyc F.moore.conn col F.moore.deg F.moore.card (x : V)
      (sigmaMap G col w x)
    omega
  have h0 : (pointGraph G col).dist x (sigmaMap G col w x) ≠ 0 := by
    intro h
    have e : (⟨x, hx⟩ : oppSet G col w) = ⟨sigmaMap G col w x, hσ⟩ :=
      Subtype.ext (Subtype.ext (F.moore.conn.dist_eq_zero_iff.mp (by rw [(hd _ _ 0).mp h])))
    rw [← e, SimpleGraph.dist_self] at h4
    omega
  have h1 : (pointGraph G col).dist x (sigmaMap G col w x) ≠ 1 := by
    intro h
    have hadj : (oppGraph G col w).Adj ⟨x, hx⟩ ⟨sigmaMap G col w x, hσ⟩ :=
      (SimpleGraph.dist_eq_one_iff_adj.mp h : (pointGraph G col).Adj x _)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at h4
    omega
  have h2 : (pointGraph G col).dist x (sigmaMap G col w x) ≠ 2 := by
    intro h
    obtain ⟨a, hxa, haσ⟩ := exists_adj_adj_of_dist_two (point_dist F.moore.conn col x _).2 h
    have haO : (pointGraph G col).dist w a ≠ 3 := fun ha3 => by
      have := SimpleGraph.dist_le (G := oppGraph G col w)
        (.cons (show (oppGraph G col w).Adj ⟨x, hx⟩ ⟨a, ha3⟩ from hxa)
          (.cons (show (oppGraph G col w).Adj ⟨a, ha3⟩ ⟨sigmaMap G col w x, hσ⟩ from haσ) .nil))
      simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
      omega
    have ha2 : (pointGraph G col).dist w a = 2 := by
      have h6 : G.dist (w : V) x = 6 := (hd w x 3).mp hx
      have hxa2 : G.dist (x : V) a = 2 := (hA x a).mp hxa
      have tri := F.moore.conn.dist_triangle (u := (w : V)) (v := (a : V)) (w := (x : V))
      rw [SimpleGraph.dist_comm (u := (a : V)), hxa2] at tri
      have hle6 := dist_le_six F.moore.cyc F.moore.conn col F.moore.deg F.moore.card (w : V) a
      obtain ⟨n, hn⟩ := even_dist_of_col_eq F.moore.conn col (w.2.trans a.2.symm)
      have hne6 : G.dist (w : V) a ≠ 6 := fun h6' => haO ((hd w a 3).mpr h6')
      exact (hd w a 2).mpr (by omega)
    obtain ⟨x', hx', hxx', hz⟩ := F.exists_edge_of_third hx ha2 ((hA x a).mp hxa)
    obtain ⟨y', hy', hσy', hz'⟩ := F.exists_edge_of_third hσ ha2 ((hA _ a).mp haσ.symm)
    obtain ⟨-, hc⟩ := F.colour_eq_of_third_eq hx hx' hxx' hσ hy' hσy' (hz.trans hz'.symm)
    obtain ⟨h, hh⟩ : ∃ h, c x x' = h := ⟨_, rfl⟩
    have hx'r : r h x = x' := F.r_eq hr hx hx' hxx' hh
    have hy'r : r h (sigmaMap G col w x) = y' := F.r_eq hr hσ hy' hσy' (hc.symm.trans hh)
    have hy'σ : y' = sigmaMap G col w x' := by rw [← hy'r, ← hx'r, sigmaMap_r F hr haper hx]
    obtain ⟨m, -, -, y'm, zm, z4, -⟩ := F.edge hσ hy' hσy'
    rw [hz'] at zm z4
    have hay' : (pointGraph G col).Adj a y' := by
      rw [hA]
      refine dist_eq_two_of_adj_adj F.moore.conn col (fun e => ?_) (a.2.trans y'.2.symm) zm y'm
      rw [e, (hd w y' 3).mp hy'] at z4
      omega
    have hle2 : (pointGraph G col).dist x y' ≤ 2 :=
      SimpleGraph.dist_le (.cons hxa (.cons hay' .nil))
    obtain ⟨i, k, hih, hhk, hik⟩ :=
      (by decide : ∀ h : Fin 3, ∃ i k : Fin 3, i ≠ h ∧ h ≠ k ∧ i ≠ k) h
    have hP := (paths_to_sigmaMap F hr haper hx' hih hhk hik).1
    have hxx : r h x' = x := by rw [← hx'r, F.r_invol hr hx]
    rw [hxx, ← hy'σ] at hP
    have h3 := dist_three_of_word F hr hx hih hih.symm
    rw [hP] at h3
    omega
  omega

include F hr haper in
theorem adj_third_sigmaMap {γ δ : {v : V // col v = false}} (hγ : γ ∈ oppSet G col w)
    (hδ : δ ∈ oppSet G col w) (hγδ : (pointGraph G col).Adj γ δ) :
    (pointGraph G col).Adj (z γ δ) (z (sigmaMap G col w γ) (sigmaMap G col w δ)) := by
  have hd := point_dist_eq_iff F.moore.conn col
  have hA := point_adj_iff F.moore.conn col
  have hV : ∀ {a b : {v : V // col v = false}}, a ≠ b → (a : V) ≠ b :=
    fun h h' => h (Subtype.ext h')
  have f : ∀ {x : {v : V // col v = false}}, (pointGraph G col).dist w x = 3 →
      G.dist (w : V) x = 6 := fun hx => (hd w _ 3).mp hx
  have tri := fun {u v t : V} => F.moore.conn.dist_triangle (u := u) (v := v) (w := t)
  have adj1 : ∀ {u v : V}, G.Adj u v → G.dist u v = 1 :=
    fun h => SimpleGraph.dist_eq_one_iff_adj.mpr h
  obtain ⟨j, hj⟩ : ∃ j, c γ δ = j := ⟨_, rfl⟩
  have hδr : r j γ = δ := F.r_eq hr hγ hδ hγδ hj
  obtain ⟨i, k, hij, hjk, hik⟩ :=
    (by decide : ∀ j : Fin 3, ∃ i k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k) j
  obtain ⟨hσi, hσk, -, -⟩ := paths_to_sigmaMap F hr haper hγ hij hjk hik
  rw [hδr] at hσi hσk
  have hγ'O := sigmaMap_mem F hr haper hγ
  have hδ'O := sigmaMap_mem F hr haper hδ
  have hγ'δ' := (adj_sigmaMap_iff F hr haper hγ hδ).mpr hγδ
  have dδγ' : G.dist (δ : V) (sigmaMap G col w γ) = 6 := by
    rw [← hσi]
    exact (hd _ _ 3).mp (dist_three_of_word F hr hδ hij hij.symm)
  have dγγ' : G.dist (γ : V) (sigmaMap G col w γ) = 6 := (hd _ _ 3).mp (dist_sigmaMap F hr haper hγ)
  have dδδ' : G.dist (δ : V) (sigmaMap G col w δ) = 6 := (hd _ _ 3).mp (dist_sigmaMap F hr haper hδ)
  obtain ⟨m, Nm, γm, δm, Am, A4, -⟩ := F.edge hγ hδ hγδ
  obtain ⟨m', Nm', γ'm', δ'm', Bm', B4, -⟩ := F.edge hγ'O hδ'O hγ'δ'
  have hAγ : (z γ δ : V) ≠ γ := fun e => by rw [e, f hγ] at A4; omega
  have hAδ : (z γ δ : V) ≠ δ := fun e => by rw [e, f hδ] at A4; omega
  have dδA : G.dist (δ : V) (z γ δ) = 2 :=
    dist_eq_two_of_adj_adj F.moore.conn col hAδ.symm (δ.2.trans (z γ δ).2.symm) δm Am
  have dAγ' : G.dist (z γ δ : V) (sigmaMap G col w γ) = 4 := by
    have hm5 : G.dist (sigmaMap G col w γ : V) m = 5 :=
      dist_eq_five_of_adj F.moore col (by rw [SimpleGraph.dist_comm]; exact dδγ') δm
    rw [SimpleGraph.dist_comm]
    rcases dist_adj F.moore.conn col Am.symm (sigmaMap G col w γ : V) with h | h
    · exfalso
      refine not_three_far_on_line F.moore col (by rw [SimpleGraph.dist_comm]; exact dγγ')
        (by rw [SimpleGraph.dist_comm]; exact dδγ') (by omega) γm δm Am (hV hγδ.ne) hAγ.symm
        hAδ.symm
    · omega
  obtain ⟨n₂, γ'n₂, hn₂⟩ := pred_exists F.moore.conn (show G.dist (z γ δ : V)
    (sigmaMap G col w γ) = 3 + 1 from dAγ')
  obtain ⟨y, n₂y, hy⟩ := pred_exists F.moore.conn (show G.dist (z γ δ : V) n₂ = 2 + 1 from hn₂)
  have dyγ' : G.dist y (sigmaMap G col w γ) ≤ 2 := by
    have := tri (u := y) (v := n₂) (t := (sigmaMap G col w γ : V))
    rw [adj1 n₂y.symm, SimpleGraph.dist_comm (u := n₂), adj1 γ'n₂] at this
    exact this
  have dδy : G.dist (δ : V) y = 4 := by
    have h1 := tri (u := (δ : V)) (v := (z γ δ : V)) (t := y)
    have h2 := tri (u := (δ : V)) (v := y) (t := (sigmaMap G col w γ : V))
    omega
  obtain ⟨h₁, a01, -⟩ := hr i δ hδ
  obtain ⟨h₂, a12, -⟩ := hr j (r i δ) h₁
  obtain ⟨h₁', a01', -⟩ := hr k δ hδ
  obtain ⟨h₂', a12', -⟩ := hr j (r k δ) h₁'
  obtain ⟨-, a23, -⟩ := hr i (r j (r i δ)) h₂
  obtain ⟨-, a23', -⟩ := hr k (r j (r k δ)) h₂'
  rw [hσi] at a23
  rw [hσk] at a23'
  obtain ⟨Li, -, v₂Li, γ'Li, -⟩ := F.edge h₂ hγ'O a23
  obtain ⟨Lk, -, v₂Lk, γ'Lk, -⟩ := F.edge h₂' hγ'O a23'
  have hv₂ : r i (sigmaMap G col w γ) = r j (r i δ) := by rw [← hσi, F.r_invol hr h₂]
  have hv₂' : r k (sigmaMap G col w γ) = r j (r k δ) := by rw [← hσk, F.r_invol hr h₂']
  have hδ' : sigmaMap G col w δ = r j (sigmaMap G col w γ) := by
    rw [← hδr, sigmaMap_r F hr haper hγ]
  have hcol : ∀ {a b : Fin 3}, a ≠ b → r a (sigmaMap G col w γ) ≠ r b (sigmaMap G col w γ) :=
    fun hab e => hab ((hr _ _ hγ'O).2.2.symm.trans ((congrArg (c (sigmaMap G col w γ)) e).trans
      (hr _ _ hγ'O).2.2))
  have hik' : r j (r i δ) ≠ r j (r k δ) := by rw [← hv₂, ← hv₂']; exact hcol hik
  have hij' : r j (r i δ) ≠ sigmaMap G col w δ := by rw [← hv₂, hδ']; exact hcol hij
  have hkj' : r j (r k δ) ≠ sigmaMap G col w δ := by rw [← hv₂', hδ']; exact hcol hjk.symm
  have hLik : Li ≠ Lk := fun e => not_three_far_on_line F.moore col (f h₂) (f h₂') (f hγ'O) v₂Li
    (by rw [e]; exact v₂Lk) γ'Li (hV hik') (hV a23.ne) (hV a23'.ne)
  have hLim : Li ≠ m' := fun e => not_three_far_on_line F.moore col (f h₂) (f hγ'O) (f hδ'O) v₂Li
    (by rw [e]; exact γ'm') (by rw [e]; exact δ'm') (hV a23.ne) (hV hij') (hV hγ'δ'.ne)
  have hLkm : Lk ≠ m' := fun e => not_three_far_on_line F.moore col (f h₂') (f hγ'O) (f hδ'O)
    v₂Lk (by rw [e]; exact γ'm') (by rw [e]; exact δ'm') (hV a23'.ne) (hV hkj') (hV hγ'δ'.ne)
  have hN : G.neighborFinset (sigmaMap G col w γ : V) = {Li, Lk, m'} :=
    neighborFinset_eq F.moore γ'Li.symm γ'Lk.symm γ'm'.symm hLik hLim hLkm
  have hn₂N : n₂ ∈ G.neighborFinset (sigmaMap G col w γ : V) :=
    (SimpleGraph.mem_neighborFinset _ _ _).mpr γ'n₂
  rw [hN] at hn₂N
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn₂N
  have hnot : ∀ {l : Fin 3} {L : V}, (pointGraph G col).dist w (r l δ) = 3 →
      (pointGraph G col).Adj δ (r l δ) → (pointGraph G col).Adj (r l δ) (r j (r l δ)) →
      G.Adj (r j (r l δ) : V) L → G.Adj (sigmaMap G col w γ : V) L → G.Adj L y →
      G.dist (r j (r l δ) : V) (sigmaMap G col w γ) = 2 → False := by
    intro l L hl1 hδl hl12 v₂L γ'L Ly hv₂γ'
    have dδL : G.dist (δ : V) L = 4 + 1 := dist_eq_five_of_adj F.moore col dδγ' γ'L
    have dδv₁ : G.dist (δ : V) (r l δ) = 2 := (hA _ _).mp hδl
    have dv₁v₂ : G.dist (r l δ : V) (r j (r l δ)) = 2 := (hA _ _).mp hl12
    have dδv₂ : G.dist (δ : V) (r j (r l δ)) = 4 := by
      have h1 := tri (u := (δ : V)) (v := (r l δ : V)) (t := (r j (r l δ) : V))
      have h2 := tri (u := (δ : V)) (v := (r j (r l δ) : V)) (t := (sigmaMap G col w γ : V))
      omega
    have hyv : y = r j (r l δ) :=
      pred_unique F.moore.cyc F.moore.conn (k := 4) (by norm_num) dδL Ly v₂L.symm dδy dδv₂
    rw [hyv] at hy
    have e := eq_of_mid F.moore dδv₂ dδA hy dδv₁ dv₁v₂
    have hl6 := f hl1
    rw [← e] at hl6
    omega
  rcases hn₂N with rfl | rfl | rfl
  · exact absurd (hnot h₁ a01 a12 v₂Li γ'Li n₂y ((hA _ _).mp a23)) id
  · exact absurd (hnot h₁' a01' a12' v₂Lk γ'Lk n₂y ((hA _ _).mp a23')) id
  ·
    have hyN : y ∈ G.neighborFinset n₂ := (SimpleGraph.mem_neighborFinset _ _ _).mpr n₂y
    rw [Nm'] at hyN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyN
    rcases hyN with h | h | h
    · rw [h] at dδy
      omega
    · rw [h] at dδy
      omega
    · rw [h] at hy
      exact (hA _ _).mpr hy

end CFSG.Combinatorics.AperiodicOppositeComponents

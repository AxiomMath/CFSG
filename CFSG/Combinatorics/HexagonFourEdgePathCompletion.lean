module

public import CFSG.Combinatorics.HexagonFourEdgePathSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonOppositeEdge

namespace CFSG.Combinatorics.HexagonFourEdgePath

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
theorem nodup_six {a b c d e f : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (haf : a ≠ f) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f) (hcd : c ≠ d)
    (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    [a, b, c, d, e, f].Nodup := by
  simp [hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef]

theorem four_path_completion (H : MooreHyp G) (col : G.Coloring Bool)
    {w : {v : V // col v = false}} {ℓ : Fin 3 → V} (hℓ : Function.Injective ℓ)
    (hwℓ : ∀ i, G.Adj (w : V) (ℓ i)) {p : Fin 3 → Fin 2 → {v : V // col v = false}}
    (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i)) (hpw : ∀ i e, p i e ≠ w)
    (hp : ∀ i, Function.Injective (p i))
    {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
    {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
    {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
    (hdata : IsFrameData G col w p z q c ε) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {v₀ v₁ v₂ v₃ v₄ : {v : V // col v = false}}
    (h₀ : (pointGraph G col).dist w v₀ = 3) (h₁ : (pointGraph G col).dist w v₁ = 3)
    (h₂ : (pointGraph G col).dist w v₂ = 3) (h₃ : (pointGraph G col).dist w v₃ = 3)
    (h₄ : (pointGraph G col).dist w v₄ = 3) (h01 : (pointGraph G col).Adj v₀ v₁)
    (h12 : (pointGraph G col).Adj v₁ v₂) (h23 : (pointGraph G col).Adj v₂ v₃)
    (h34 : (pointGraph G col).Adj v₃ v₄) (hnd : [v₀, v₁, v₂, v₃, v₄].Nodup)
    (hc₀ : c v₀ v₁ = i) (hc₁ : c v₁ v₂ = j) (hc₂ : c v₂ v₃ = k) (hc₃ : c v₃ v₄ = i) :
    ∃ u, ((pointGraph G col).dist w u = 3 ∧ (pointGraph G col).Adj v₀ u ∧
        (pointGraph G col).Adj v₄ u) ∧
      (∀ u', (pointGraph G col).dist w u' = 3 → (pointGraph G col).Adj v₀ u' →
        (pointGraph G col).Adj v₄ u' → u' = u) ∧
      [v₀, v₁, v₂, v₃, v₄, u].Nodup := by
  have hd := point_dist_eq_iff H.conn col
  have hA := point_adj_iff H.conn col
  obtain ⟨hsep, hrep⟩ := opposite_edge_equal_label_separation_and_four_path_repeat G H col w ℓ
    hℓ hwℓ p hpℓ hpw hp z q c ε hdata
  have f₀ : G.dist (w : V) v₀ = 6 := (hd w v₀ 3).mp h₀
  have f₁ : G.dist (w : V) v₁ = 6 := (hd w v₁ 3).mp h₁
  have f₂ : G.dist (w : V) v₂ = 6 := (hd w v₂ 3).mp h₂
  have f₃ : G.dist (w : V) v₃ = 6 := (hd w v₃ 3).mp h₃
  have f₄ : G.dist (w : V) v₄ = 6 := (hd w v₄ 3).mp h₄
  have hV : ∀ {a b : {v : V // col v = false}}, a ≠ b → (a : V) ≠ b :=
    fun h h' => h (Subtype.ext h')
  have n02 : v₀ ≠ v₂ := by
    rintro rfl
    simp at hnd
  have n03 : v₀ ≠ v₃ := by
    rintro rfl
    simp at hnd
  have n04 : v₀ ≠ v₄ := by
    rintro rfl
    simp at hnd
  have n13 : v₁ ≠ v₃ := by
    rintro rfl
    simp at hnd
  have n14 : v₁ ≠ v₄ := by
    rintro rfl
    simp at hnd
  have n24 : v₂ ≠ v₄ := by
    rintro rfl
    simp at hnd
  obtain ⟨m₀, N₀, v₀m₀, v₁m₀, am₀, a4, t2, at2, -, -, -⟩ := frame_edge H col hdata h₀ h₁ h01
  obtain ⟨m₁, -, v₁m₁, v₂m₁, -, -, -, -, -, -, -⟩ := frame_edge H col hdata h₁ h₂ h12
  obtain ⟨m₂, -, v₂m₂, v₃m₂, -, -, -, -, -, -, -⟩ := frame_edge H col hdata h₂ h₃ h23
  obtain ⟨m₃, N₃, v₃m₃, v₄m₃, bm₃, b4, -, bt2, -, -, -⟩ := frame_edge H col hdata h₃ h₄ h34
  have hq : q v₀ v₁ = q v₃ v₄ :=
    hrep v₀ h₀ v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ h01 h12 h23 h34 hnd (hc₀.trans hc₃.symm)
  rw [← hq] at bt2
  have m01 : m₀ ≠ m₁ := fun h => not_three_far_on_line H col f₀ f₁ f₂ v₀m₀ v₁m₀
    (by rw [h]; exact v₂m₁) (hV h01.ne) (hV n02) (hV h12.ne)
  have m12 : m₁ ≠ m₂ := fun h => not_three_far_on_line H col f₁ f₂ f₃ v₁m₁ v₂m₁
    (by rw [h]; exact v₃m₂) (hV h12.ne) (hV n13) (hV h23.ne)
  have m23 : m₂ ≠ m₃ := fun h => not_three_far_on_line H col f₂ f₃ f₄ v₂m₂ v₃m₂
    (by rw [h]; exact v₄m₃) (hV h23.ne) (hV n24) (hV h34.ne)
  obtain ⟨-, -, d13, d1m₃, d14⟩ := dist_of_path_six H col v₁m₁ v₂m₁.symm v₂m₂ v₃m₂.symm v₃m₃
    v₄m₃.symm (hV h12.ne.symm) m12.symm (hV h23.ne.symm) m23.symm (hV h34.ne.symm)
  obtain ⟨-, -, -, -, d30⟩ := dist_of_path_six H col v₃m₂ v₂m₂.symm v₂m₁ v₁m₁.symm v₁m₀
    v₀m₀.symm (hV h23.ne) m12 (hV h12.ne) m01 (hV h01.ne)
  have d1b : G.dist (v₁ : V) (z v₃ v₄) = 6 := by
    rcases dist_adj H.conn col bm₃.symm (v₁ : V) with h | h
    · omega
    · exfalso
      have hb := pred_unique H.cyc H.conn (k := 4) (by norm_num) d1m₃ bm₃.symm v₃m₃.symm
        (by omega) d13
      rw [hb] at b4
      omega
  obtain ⟨na, ana, tna⟩ := exists_adj_adj_of_dist_eq_two H.conn at2
  obtain ⟨nb, bnb, tnb⟩ := exists_adj_adj_of_dist_eq_two H.conn bt2
  have nab : na ≠ nb := by
    intro h
    have e1 : G.dist (v₁ : V) (z v₀ v₁) ≤ 2 := by
      have := H.conn.dist_triangle (u := (v₁ : V)) (v := m₀) (w := (z v₀ v₁ : V))
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr v₁m₀, SimpleGraph.dist_eq_one_iff_adj.mpr am₀.symm]
        at this
      omega
    have e2 : G.dist (z v₀ v₁ : V) (z v₃ v₄) ≤ 2 := by
      have := H.conn.dist_triangle (u := (z v₀ v₁ : V)) (v := na) (w := (z v₃ v₄ : V))
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ana, h, SimpleGraph.dist_eq_one_iff_adj.mpr bnb.symm]
        at this
      omega
    have e3 := H.conn.dist_triangle (u := (v₁ : V)) (v := (z v₀ v₁ : V)) (w := (z v₃ v₄ : V))
    omega
  have m3nb : m₃ ≠ nb := by
    intro h
    have ht : (q v₀ v₁ : V) ∈ G.neighborFinset m₃ := by
      rw [h]
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr tnb.symm
    rw [N₃] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with h' | h' | h'
    · rw [h'] at t2
      omega
    · rw [h'] at t2
      omega
    · rw [h'] at t2
      omega
  obtain ⟨-, -, -, -, da4⟩ := dist_of_path_six H col ana tna.symm tnb bnb.symm bm₃ v₄m₃.symm
    (fun h => by rw [h] at t2; omega) nab.symm (fun h => by rw [h] at b4; omega) m3nb
    (fun h => by rw [← h] at b4; omega)
  have d4m₀ : G.dist (v₄ : V) m₀ = 4 + 1 :=
    dist_eq_five_of_adj H col (by rw [SimpleGraph.dist_comm]; exact d14) v₁m₀
  obtain ⟨t₀, m₀t₀, ht₀⟩ := pred_exists H.conn d4m₀
  have ht₀N : t₀ ∈ G.neighborFinset m₀ := (SimpleGraph.mem_neighborFinset _ _ _).mpr m₀t₀
  rw [N₀] at ht₀N
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht₀N
  have d04 : G.dist (v₀ : V) v₄ = 4 := by
    rw [SimpleGraph.dist_comm]
    rcases ht₀N with h | h | h
    · rw [← h]
      exact ht₀
    · rw [h, SimpleGraph.dist_comm] at ht₀
      omega
    · rw [h, SimpleGraph.dist_comm] at ht₀
      omega
  obtain ⟨u₀, hu4, hu0, huniq⟩ := exists_unique_lower H col d04
  obtain ⟨u, rfl⟩ : ∃ u : {v : V // col v = false}, (u : V) = u₀ := by
    have h := (even_dist_iff H.conn col (v₀ : V) u₀).mp (by rw [hu0]; decide)
    rw [Bool.coe_iff_coe, v₀.2] at h
    exact ⟨⟨u₀, h.symm⟩, rfl⟩
  have hu6 : G.dist (w : V) u = 6 := by
    have hle := dist_le_six H.cyc H.conn col H.deg H.card (w : V) u
    have hge : G.dist (w : V) v₀ ≤ G.dist (w : V) u + G.dist (u : V) v₀ := H.conn.dist_triangle
    rw [SimpleGraph.dist_comm (u := (u : V)) (v := (v₀ : V)), hu0] at hge
    obtain ⟨n, hn⟩ := even_dist_of_col_eq H.conn col (w.2.trans u.2.symm)
    by_contra hne
    have hu4' : G.dist (w : V) u = 4 := by omega
    have hside : ∀ {x : {v : V // col v = false}}, (pointGraph G col).dist w x = 3 →
        G.dist (x : V) u = 2 → ∃ x' : {v : V // col v = false},
          (pointGraph G col).dist w x' = 3 ∧ (pointGraph G col).Adj x x' ∧ z x x' = u := by
      intro x hx hxu
      have hx6 : G.dist (w : V) x = 6 := (hd w x 3).mp hx
      obtain ⟨mu, hxmu, humu⟩ := exists_adj_adj_of_dist_eq_two H.conn hxu
      obtain ⟨a', x', hNmu, -, hx', hx'x⟩ := far_lines H col w x hx mu hxmu
      have hx'mu : G.Adj (x' : V) mu := by
        have h : (x' : V) ∈ G.neighborFinset mu := by rw [hNmu]; simp
        exact ((SimpleGraph.mem_neighborFinset _ _ _).mp h).symm
      have hxx' : (pointGraph G col).Adj x x' := (hA _ _).mpr
        (dist_eq_two_of_adj_adj H.conn col (fun h => hx'x (Subtype.ext h).symm)
          (x.2.trans x'.2.symm) hxmu hx'mu)
      refine ⟨x', hx', hxx', ?_⟩
      have hN := (hdata x hx x' hx' hxx').1 mu hxmu hx'mu
      have hzmu : G.Adj (z x x' : V) mu := by
        have h : (z x x' : V) ∈ G.neighborFinset mu := by rw [hN]; simp
        exact ((SimpleGraph.mem_neighborFinset _ _ _).mp h).symm
      obtain ⟨_m, -, -, -, -, hz4, -⟩ := frame_edge H col hdata hx hx' hxx'
      exact Subtype.ext (pred_unique H.cyc H.conn (k := 4) (by norm_num)
        (dist_eq_five_of_adj H col hx6 hxmu) hzmu.symm humu.symm hz4 hu4')
    obtain ⟨v₀', hv₀', h00', hz0⟩ := hside h₀ hu0
    obtain ⟨v₄', hv₄', h44', hz4⟩ := hside h₄ hu4
    have hq04 : q v₄ v₄' = q v₀ v₀' := by
      have h1 := ((hdata v₀ h₀ v₀' hv₀' h00').2.1 (q v₀ v₀')).mpr rfl
      rw [hz0, ← hz4] at h1
      exact (((hdata v₄ h₄ v₄' hv₄' h44').2.1 (q v₀ v₀')).mp h1).symm
    have hh : c v₀ v₀' = c v₄ v₄' := by
      have e := (hdata v₀ h₀ v₀' hv₀' h00').2.2
      rw [← hq04, (hdata v₄ h₄ v₄' hv₄' h44').2.2] at e
      exact (label_injective H col hℓ hwℓ hpℓ hpw hp e).1.symm
    have hhi : c v₀ v₀' ≠ i := by
      intro h
      have e := frame_colour_unique H col hℓ hwℓ hpℓ hpw hp hdata h₀ hv₀' h₁ h00' h01
        (h.trans hc₀.symm)
      rw [e] at hz0
      rw [hz0, SimpleGraph.dist_comm] at da4
      omega
    have hjk' : c v₀ v₀' = j ∨ c v₀ v₀' = k := by
      have key : ∀ h i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → h ≠ i → h = j ∨ h = k := by
        decide
      exact key _ _ _ _ hij hjk hik hhi
    rcases hjk' with hj | hk
    ·
      have hc4 : c v₄ v₄' = j := hh ▸ hj
      have n43 : v₄' ≠ v₃ := by
        rintro rfl
        have hs := (frame_symm H col hℓ hwℓ hpℓ hpw hp hdata h₃ h₄ h34).2.2.1
        rw [hc4, hc₃] at hs
        exact hij hs.symm
      have n42 : v₄' ≠ v₂ := by
        rintro rfl
        exact no_far_triangle H col f₂ f₃ f₄ ((hA _ _).mp h23) ((hA _ _).mp h34)
          ((hA _ _).mp h44')
      have n41 : v₄' ≠ v₁ := by
        rintro rfl
        have h' := (hA _ _).mp h44'
        rw [SimpleGraph.dist_comm] at h'
        omega
      have hnd' : [v₁, v₂, v₃, v₄, v₄'].Nodup := nodup_five h12.ne n13 n14 n41.symm h23.ne n24
        n42.symm h34.ne n43.symm h44'.ne
      have hq1 := hrep v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ v₄' hv₄' h12 h23 h34 h44' hnd'
        (hc₁.trans hc4.symm)
      have hne : s(v₀, v₀') ≠ s(v₁, v₂) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
        · exact h01.ne h'
        · exact n02 h'
      exact (hsep v₀ h₀ v₀' hv₀' v₁ h₁ v₂ h₂ h00' h12 hne (hq1.trans hq04).symm).2 v₀ (by simp)
        v₁ (by simp) h01
    ·
      have hc32 : c v₃ v₂ = k :=
        (frame_symm H col hℓ hwℓ hpℓ hpw hp hdata h₂ h₃ h23).2.2.1.trans hc₂
      have n01' : v₀' ≠ v₁ := by
        rintro rfl
        exact hik (hc₀.symm.trans hk)
      have n02' : v₀' ≠ v₂ := by
        rintro rfl
        exact no_far_triangle H col f₀ f₁ f₂ ((hA _ _).mp h01) ((hA _ _).mp h12)
          (by rw [SimpleGraph.dist_comm]; exact (hA _ _).mp h00')
      have n03' : v₀' ≠ v₃ := by
        rintro rfl
        have h' := (hA _ _).mp h00'
        rw [SimpleGraph.dist_comm] at h'
        omega
      have hnd' : [v₃, v₂, v₁, v₀, v₀'].Nodup := nodup_five h23.ne.symm n13.symm n03.symm
        n03'.symm h12.ne.symm n02.symm n02'.symm h01.ne.symm n01'.symm h00'.ne
      have hq1 := hrep v₃ h₃ v₂ h₂ v₁ h₁ v₀ h₀ v₀' hv₀' h23.symm h12.symm h01.symm h00' hnd'
        (hc32.trans hk.symm)
      have hne : s(v₄, v₄') ≠ s(v₃, v₂) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
        · exact h34.ne h'.symm
        · exact n24 h'.symm
      exact (hsep v₄ h₄ v₄' hv₄' v₃ h₃ v₂ h₂ h44' h23.symm hne (hq04.trans hq1.symm)).2 v₄
        (by simp) v₃ (by simp) h34.symm
  have nu0 : u ≠ v₀ := by
    rintro rfl
    rw [SimpleGraph.dist_self] at hu0
    omega
  have nu1 : u ≠ v₁ := by
    rintro rfl
    rw [SimpleGraph.dist_comm] at hu4
    omega
  have nu2 : u ≠ v₂ := by
    rintro rfl
    exact no_far_triangle H col f₀ f₁ f₂ ((hA _ _).mp h01) ((hA _ _).mp h12)
      (by rw [SimpleGraph.dist_comm]; exact hu0)
  have nu3 : u ≠ v₃ := by
    rintro rfl
    rw [SimpleGraph.dist_comm] at hu0
    omega
  have nu4 : u ≠ v₄ := by
    rintro rfl
    rw [SimpleGraph.dist_self] at hu4
    omega
  refine ⟨u, ⟨(hd w u 3).mpr hu6, (hA _ _).mpr hu0, (hA _ _).mpr hu4⟩,
    fun u' _ h0u' h4u' => Subtype.ext (huniq u' ((hA _ _).mp h4u') ((hA _ _).mp h0u')),
    nodup_six h01.ne n02 n03 n04 nu0.symm h12.ne n13 n14 nu1.symm h23.ne n24 nu2.symm h34.ne
      nu3.symm nu4.symm⟩

end CFSG.Combinatorics.HexagonFourEdgePath

module

public import CFSG.Geometry.GeneralizedQuadrangles.Counting.Variance

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section Vocabulary

variable (Γ : SimpleGraph V) (c : Γ.Coloring (Fin 2))

@[expose] def ptPerp (X : Set V) : Set V := {z | c z = 0 ∧ ∀ x ∈ X, Γ.dist z x ≤ 2}

@[expose] def starLine (x y : V) : Set V := ptPerp Γ c (ptPerp Γ c {x, y})

@[expose] def IsStarLine (X : Set V) : Prop :=
  ∃ x y, c x = 0 ∧ c y = 0 ∧ x ≠ y ∧ X = starLine Γ c x y

@[expose] def IsHypLine (X : Set V) : Prop :=
  ∃ x y, c x = 0 ∧ Γ.dist x y = 4 ∧ X = starLine Γ c x y

@[expose] def IsStarCollinear (x y z : V) : Prop :=
  ∃ X, IsStarLine Γ c X ∧ x ∈ X ∧ y ∈ X ∧ z ∈ X

@[expose] def IsLinearVariety (X : Set V) : Prop :=
  (∀ x ∈ X, c x = 0) ∧ ∀ x ∈ X, ∀ y ∈ X, x ≠ y → starLine Γ c x y ⊆ X

@[expose] def IsProperVariety (X : Set V) : Prop :=
  IsLinearVariety Γ c X ∧ ∃ w, c w = 0 ∧ w ∉ X

@[expose] def IsStarPlane (X : Set V) : Prop :=
  IsProperVariety Γ c X ∧ ∃ x ∈ X, ∃ y ∈ X, ∃ z ∈ X, ¬ IsStarCollinear Γ c x y z

@[expose] def IsOvoid (X : Set V) : Prop :=
  (∀ x ∈ X, c x = 0) ∧ ∀ L, c L = 1 → (Γ.neighborSet L ∩ X).ncard = 1

@[expose] def IsAbsPlane (X : Set V) : Prop := ∃ u, c u = 0 ∧ X = ptPerp Γ c {u}

@[expose] def IsNonabsPlane (X : Set V) : Prop := IsStarPlane Γ c X ∧ IsOvoid Γ c X

@[expose] def TalliniCondPrime : Prop :=
  ∀ x y z, c x = 0 → c y = 0 → c z = 0 → ¬ IsStarCollinear Γ c x y z →
    ∃ X, IsStarPlane Γ c X ∧ x ∈ X ∧ y ∈ X ∧ z ∈ X

@[expose] def TalliniCond : Prop :=
  ∀ L L', IsStarLine Γ c L → IsStarLine Γ c L' →
    (∃ X, IsProperVariety Γ c X ∧ L ∪ L' ⊆ X) →
    ∃ X, IsProperVariety Γ c X ∧ ptPerp Γ c L ∪ ptPerp Γ c L' ⊆ X

end Vocabulary

section Aux

variable {Γ : SimpleGraph V}

private theorem color_zero_of_mem_trace_aux (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {x y z : V} (hx : c x = 0)
    (hz : z ∈ traceSet Γ x y) : c z = 0 := by
  rw [← hx]
  exact (hP.eq_iff_even_dist c z x).2 (by
    rw [SimpleGraph.dist_comm, hz.1]
    exact ⟨1, by norm_num⟩)

private theorem mem_traceSet_of_dist_le_two_aux (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {x y z : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) (hz0 : c z = 0)
    (hzx : Γ.dist z x ≤ 2) (hzy : Γ.dist z y ≤ 2) :
    z ∈ traceSet Γ x y := by
  have hy0 : c y = 0 := by
    rw [← hx]
    exact ((hP.eq_iff_even_dist c x y).2 (by rw [hxy]; exact ⟨2, by norm_num⟩)).symm
  have hx2 : Γ.dist z x = 2 := by
    have heven : Even (Γ.dist z x) :=
      (hP.eq_iff_even_dist c z x).1 (by rw [hz0, hx])
    have hne0 : Γ.dist z x ≠ 0 := by
      intro h0
      have hzx_eq : z = x := (hP.connected.dist_eq_zero_iff).mp h0
      rw [hzx_eq] at hzy
      omega
    obtain ⟨k, hk⟩ := heven
    omega
  have hy2 : Γ.dist z y = 2 := by
    have heven : Even (Γ.dist z y) :=
      (hP.eq_iff_even_dist c z y).1 (by rw [hz0, hy0])
    have hne0 : Γ.dist z y ≠ 0 := by
      intro h0
      have hzy_eq : z = y := (hP.connected.dist_eq_zero_iff).mp h0
      rw [hzy_eq, SimpleGraph.dist_comm] at hzx
      omega
    obtain ⟨k, hk⟩ := heven
    omega
  exact ⟨by rw [SimpleGraph.dist_comm]; exact hx2,
    by rw [SimpleGraph.dist_comm]; exact hy2⟩

private theorem ptPerp_pair_eq_traceSet_aux (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {x y : V} (hx : c x = 0) (hxy : Γ.dist x y = 4) :
    ptPerp Γ c ({x, y} : Set V) = traceSet Γ x y := by
  ext z
  constructor
  · rintro ⟨hz0, hz⟩
    exact mem_traceSet_of_dist_le_two_aux hP c hx hxy hz0
      (hz x (by simp)) (hz y (by simp))
  · intro hz
    refine ⟨color_zero_of_mem_trace_aux hP hx hz, ?_⟩
    intro w hw
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · subst hw
      rw [SimpleGraph.dist_comm]
      exact le_of_eq hz.1
    · subst hw
      rw [SimpleGraph.dist_comm]
      exact le_of_eq hz.2

end Aux

section Basic

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem ptPerp_spanSet_eq_traceSet_aux (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {x y : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) :
    ptPerp Γ c (spanSet Γ x y) = traceSet Γ x y := by
  ext z
  constructor
  · rintro ⟨hz0, hz⟩
    exact mem_traceSet_of_dist_le_two_aux hP c hx hxy hz0
      (hz x (left_mem_spanSet hxy)) (hz y (right_mem_spanSet hxy))
  · intro hz
    refine ⟨color_zero_of_mem_trace_aux hP hx hz, ?_⟩
    intro w hw
    have h2 : Γ.dist w z = 2 :=
      dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hw hz
    rw [SimpleGraph.dist_comm] at h2
    omega

private theorem ptPerp_traceSet_eq_spanSet_aux (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {x y : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) :
    ptPerp Γ c (traceSet Γ x y) = spanSet Γ x y := by
  ext z
  constructor
  · rintro ⟨-, hz⟩
    exact hz
  · intro hz
    exact ⟨color_eq_zero_of_mem_span hP hT hx hxy hz, hz⟩

private theorem ptPerp_pair_eq_neighborSet_aux (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {x y : V} (hx : c x = 0) (hxy : Γ.dist x y = 2) :
    ptPerp Γ c ({x, y} : Set V) = Γ.neighborSet (commonNeighbor hP hxy) := by
  classical
  let K := commonNeighbor hP hxy
  have hKx : Γ.Adj x K := commonNeighbor_adj_left hP hxy
  have hKy : Γ.Adj y K := commonNeighbor_adj_right hP hxy
  have hy0 : c y = 0 := by
    rw [← hx]
    exact ((hP.eq_iff_even_dist c x y).2 (by rw [hxy]; exact ⟨1, by norm_num⟩)).symm
  ext z
  constructor
  · rintro ⟨hz0, hz⟩
    have hzx : Γ.dist z x ≤ 2 := hz x (by simp)
    have hzy : Γ.dist z y ≤ 2 := hz y (by simp)
    by_cases hzxeq : z = x
    · rw [hzxeq]
      exact hKx.symm
    by_cases hzyeq : z = y
    · rw [hzyeq]
      exact hKy.symm
    have hzx2 : Γ.dist z x = 2 := by
      have heven : Even (Γ.dist z x) :=
        (hP.eq_iff_even_dist c z x).1 (by rw [hz0, hx])
      have hne0 : Γ.dist z x ≠ 0 := fun h0 =>
        hzxeq ((hP.connected.dist_eq_zero_iff).mp h0)
      obtain ⟨k, hk⟩ := heven
      omega
    have hzy2 : Γ.dist z y = 2 := by
      have heven : Even (Γ.dist z y) :=
        (hP.eq_iff_even_dist c z y).1 (by rw [hz0, hy0])
      have hne0 : Γ.dist z y ≠ 0 := fun h0 =>
        hzyeq ((hP.connected.dist_eq_zero_iff).mp h0)
      obtain ⟨k, hk⟩ := heven
      omega
    have hxz2 : Γ.dist x z = 2 := by rw [SimpleGraph.dist_comm]; exact hzx2
    have hyz2 : Γ.dist y z = 2 := by rw [SimpleGraph.dist_comm]; exact hzy2
    obtain ⟨w, hw, -⟩ :=
      existsUnique_commonNeighbor_of_pairwise_dist_two hP hxy hxz2 hyz2
    have hwK : w = K :=
      (existsUnique_commonNeighbor hP hxy).unique ⟨hw.1, hw.2.1⟩ ⟨hKx, hKy⟩
    exact (hwK ▸ hw.2.2).symm
  · intro hzK
    have hK1 : c K = 1 := color_eq_one_of_adj_of_color_eq_zero hx hKx
    have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hK1 hzK
    refine ⟨hz0, ?_⟩
    intro w hw
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · rw [hw]
      by_cases hzx : z = x
      · rw [hzx]
        simp
      · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hzK.symm hKx.symm hzx)
    · rw [hw]
      by_cases hzy : z = y
      · rw [hzy]
        simp
      · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hzK.symm hKy.symm hzy)

private theorem ptPerp_neighborSet_eq_aux (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {K : V} (hK : c K = 1) :
    ptPerp Γ c (Γ.neighborSet K) = Γ.neighborSet K := by
  classical
  ext z
  constructor
  · rintro ⟨hz0, hz⟩
    by_contra hznot
    have hdist3 : Γ.dist z K = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hznot h.symm) (by
        rw [hz0, hK]
        decide)
    obtain ⟨w0, hw0, -⟩ := existsUnique_proj hP hdist3
    have hNcard : 1 < (Γ.neighborSet K).ncard := by
      rw [SimpleGraph.ncard_neighborSet]
      have h3 := hT K
      omega
    obtain ⟨w1, hw1, w2, hw2, h12⟩ :=
      (Set.one_lt_ncard (s := Γ.neighborSet K)).mp hNcard
    have hw1_2 : Γ.dist z w1 = 2 := by
      have hc1 : c w1 = 0 := color_eq_zero_of_adj_of_color_eq_one hK hw1
      have hle := hz w1 hw1
      have hne0 : Γ.dist z w1 ≠ 0 := by
        intro h0
        have hzw1 : z = w1 := (hP.connected.dist_eq_zero_iff).mp h0
        exact hznot (hzw1.symm ▸ hw1)
      have hne1 : Γ.dist z w1 ≠ 1 := by
        intro h1
        have hne := c.valid (SimpleGraph.dist_eq_one_iff_adj.mp h1)
        exact hne (hz0.trans hc1.symm)
      omega
    have hw2_2 : Γ.dist z w2 = 2 := by
      have hc2 : c w2 = 0 := color_eq_zero_of_adj_of_color_eq_one hK hw2
      have hle := hz w2 hw2
      have hne0 : Γ.dist z w2 ≠ 0 := by
        intro h0
        have hzw2 : z = w2 := (hP.connected.dist_eq_zero_iff).mp h0
        exact hznot (hzw2.symm ▸ hw2)
      have hne1 : Γ.dist z w2 ≠ 1 := by
        intro h1
        have hne := c.valid (SimpleGraph.dist_eq_one_iff_adj.mp h1)
        exact hne (hz0.trans hc2.symm)
      omega
    have hw1eq : w1 = w0 :=
      (existsUnique_proj hP hdist3).unique ⟨hw1, hw1_2⟩ hw0
    have hw2eq : w2 = w0 :=
      (existsUnique_proj hP hdist3).unique ⟨hw2, hw2_2⟩ hw0
    exact h12 (hw1eq.trans hw2eq.symm)
  · intro hzK
    have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hK hzK
    refine ⟨hz0, ?_⟩
    intro w hw
    by_cases hzw : z = w
    · rw [hzw]
      simp
    · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hzK.symm hw hzw)

theorem starLine_eq_spanSet (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {x y : V} (hx : c x = 0) (hxy : Γ.dist x y = 4) :
    starLine Γ c x y = spanSet Γ x y := by
  unfold starLine
  rw [ptPerp_pair_eq_traceSet_aux hP c hx hxy]
  exact ptPerp_traceSet_eq_spanSet_aux hP hT c hx hxy

theorem starLine_eq_neighborSet (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {x y : V} (hx : c x = 0) (hxy : Γ.dist x y = 2) :
    starLine Γ c x y = Γ.neighborSet (commonNeighbor hP hxy) := by
  unfold starLine
  rw [ptPerp_pair_eq_neighborSet_aux hP c hx hxy]
  exact ptPerp_neighborSet_eq_aux hP hT c
    (color_eq_one_of_adj_of_color_eq_zero hx (commonNeighbor_adj_left hP hxy))

theorem starLine_eq_of_mem (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {x y a b : V} (hx : c x = 0) (hy : c y = 0) (hxy : x ≠ y)
    (ha : a ∈ starLine Γ c x y) (hb : b ∈ starLine Γ c x y) (hab : a ≠ b) :
    starLine Γ c a b = starLine Γ c x y := by
  classical
  have hca : c a = 0 := ha.1
  have hd2or4 : Γ.dist x y = 2 ∨ Γ.dist x y = 4 := by
    have heven : Even (Γ.dist x y) := (hP.eq_iff_even_dist c x y).1 (by rw [hx, hy])
    have hle : Γ.dist x y ≤ 4 := hP.dist_le (by norm_num) x y
    have hne0 : Γ.dist x y ≠ 0 := fun h =>
      hxy ((hP.connected.dist_eq_zero_iff).mp h)
    obtain ⟨k, hk⟩ := heven
    omega
  rcases hd2or4 with hd2 | hd4
  · have hline : starLine Γ c x y = Γ.neighborSet (commonNeighbor hP hd2) :=
      starLine_eq_neighborSet hP hT c hx hd2
    have haN : a ∈ Γ.neighborSet (commonNeighbor hP hd2) := by rw [← hline]; exact ha
    have hbN : b ∈ Γ.neighborSet (commonNeighbor hP hd2) := by rw [← hline]; exact hb
    have hab2 : Γ.dist a b = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP haN.symm hbN hab
    have hcommon : commonNeighbor hP hab2 = commonNeighbor hP hd2 :=
      (eq_commonNeighbor hP hab2 haN.symm hbN.symm).symm
    rw [starLine_eq_neighborSet hP hT c hca hab2, hcommon, hline]
  · have hspan : starLine Γ c x y = spanSet Γ x y :=
      starLine_eq_spanSet hP hT c hx hd4
    have haS : a ∈ spanSet Γ x y := by rw [← hspan]; exact ha
    have hbS : b ∈ spanSet Γ x y := by rw [← hspan]; exact hb
    obtain ⟨hab4, hspanab, -⟩ := span_eq_of_mem hP hT hd4 haS hbS hab
    rw [starLine_eq_spanSet hP hT c hca hab4, hspanab, hspan]

theorem ncard_starLine_of_dist_four (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {x y : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) : (starLine Γ c x y).ncard = t + 1 := by
  rw [starLine_eq_spanSet hP hT c hx hxy, hreg x hx y hxy,
    degree_eq_t_add_one_of_color_zero hdeg hx]

theorem ptPerp_ptPerp_starLine (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {L : Set V} (hL : IsStarLine Γ c L) :
    IsStarLine Γ c (ptPerp Γ c L) ∧ ptPerp Γ c (ptPerp Γ c L) = L := by
  classical
  obtain ⟨x, y, hx, hy, hxy, hLstar⟩ := hL
  subst L
  have hd2or4 : Γ.dist x y = 2 ∨ Γ.dist x y = 4 := by
    have heven : Even (Γ.dist x y) := (hP.eq_iff_even_dist c x y).1 (by rw [hx, hy])
    have hle : Γ.dist x y ≤ 4 := hP.dist_le (by norm_num) x y
    have hne0 : Γ.dist x y ≠ 0 := fun h =>
      hxy ((hP.connected.dist_eq_zero_iff).mp h)
    obtain ⟨k, hk⟩ := heven
    omega
  rcases hd2or4 with hd2 | hd4
  · have hline : starLine Γ c x y = Γ.neighborSet (commonNeighbor hP hd2) :=
      starLine_eq_neighborSet hP hT c hx hd2
    have hK1 : c (commonNeighbor hP hd2) = 1 :=
      color_eq_one_of_adj_of_color_eq_zero hx (commonNeighbor_adj_left hP hd2)
    have hfix : ptPerp Γ c (starLine Γ c x y) = starLine Γ c x y := by
      rw [hline]
      exact ptPerp_neighborSet_eq_aux hP hT c hK1
    refine ⟨?_, ?_⟩
    · rw [hfix]
      exact ⟨x, y, hx, hy, hxy, rfl⟩
    · rw [hfix]
      exact hfix
  · have hspan : starLine Γ c x y = spanSet Γ x y :=
      starLine_eq_spanSet hP hT c hx hd4
    have hpt : ptPerp Γ c (starLine Γ c x y) = traceSet Γ x y := by
      rw [hspan]
      exact ptPerp_spanSet_eq_traceSet_aux hP hT c hx hd4
    have ht2 : 2 ≤ t := two_le_t hP hT c hdeg
    have hTcard : (traceSet Γ x y).ncard = t + 1 := by
      rw [ncard_trace hP hd4, degree_eq_t_add_one_of_color_zero hdeg hx]
    obtain ⟨u, hu, v, hv, huv⟩ :=
      (Set.one_lt_ncard (s := traceSet Γ x y)).mp (by rw [hTcard]; omega)
    have hcu : c u = 0 := color_zero_of_mem_trace_aux hP hx hu
    have hcv : c v = 0 := color_zero_of_mem_trace_aux hP hx hv
    have huv4 : Γ.dist u v = 4 := dist_eq_four_of_mem_trace hP hd4 hu hv huv
    have hspan_sub : spanSet Γ u v ⊆ traceSet Γ x y := by
      intro z hz
      have hcz : c z = 0 := color_eq_zero_of_mem_span hP hT hcu huv4 hz
      have hux : Γ.dist u x = 2 := by rw [SimpleGraph.dist_comm]; exact hu.1
      have hvx : Γ.dist v x = 2 := by rw [SimpleGraph.dist_comm]; exact hv.1
      have huy : Γ.dist u y = 2 := by rw [SimpleGraph.dist_comm]; exact hu.2
      have hvy : Γ.dist v y = 2 := by rw [SimpleGraph.dist_comm]; exact hv.2
      have hxu : x ∈ traceSet Γ u v := ⟨hux, hvx⟩
      have hyu : y ∈ traceSet Γ u v := ⟨huy, hvy⟩
      exact mem_traceSet_of_dist_le_two_aux hP c hx hd4 hcz
        (hz x hxu) (hz y hyu)
    have hspan_card : (spanSet Γ u v).ncard = (traceSet Γ x y).ncard := by
      rw [hreg u hcu v huv4, degree_eq_t_add_one_of_color_zero hdeg hcu, hTcard]
    have hspan_eq : spanSet Γ u v = traceSet Γ x y :=
      Set.eq_of_subset_of_ncard_le hspan_sub (le_of_eq hspan_card.symm)
    have hstar_uv : starLine Γ c u v = traceSet Γ x y := by
      rw [starLine_eq_spanSet hP hT c hcu huv4, hspan_eq]
    have hstarT : IsStarLine Γ c (traceSet Γ x y) :=
      ⟨u, v, hcu, hcv, huv, hstar_uv.symm⟩
    refine ⟨?_, ?_⟩
    · rw [hpt]
      exact hstarT
    · rw [hpt, ptPerp_traceSet_eq_spanSet_aux hP hT c hx hd4]
      exact hspan.symm

theorem ncard_ptPerp_singleton (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {u : V} (hu : c u = 0) :
    (ptPerp Γ c {u}).ncard = s * t + s + 1 := by
  classical
  let A : Finset V := Finset.univ.filter fun z => Γ.dist z u = 2
  have hset : ptPerp Γ c {u} = (({u} : Finset V) : Set V) ∪ (A : Set V) := by
    ext z
    constructor
    · rintro ⟨hz0, hzu⟩
      have hzu' : Γ.dist z u ≤ 2 := hzu u rfl
      have heven : Even (Γ.dist z u) :=
        (hP.eq_iff_even_dist c z u).1 (by rw [hz0, hu])
      have hcases : Γ.dist z u = 0 ∨ Γ.dist z u = 2 := by
        obtain ⟨k, hk⟩ := heven
        omega
      rw [Set.mem_union]
      simp only [Finset.mem_coe, Finset.mem_singleton]
      rcases hcases with h0 | h2
      · left
        exact (hP.connected.dist_eq_zero_iff).mp h0
      · right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
    · intro hz
      rw [Set.mem_union] at hz
      simp only [Finset.mem_coe, Finset.mem_singleton] at hz
      rcases hz with hzu | h2
      · rw [hzu]
        refine ⟨hu, ?_⟩
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp
      · have h2' : z ∈ Finset.univ.filter (fun z => Γ.dist z u = 2) := by
          simpa [A] using h2
        obtain ⟨-, hzu2⟩ := Finset.mem_filter.mp h2' 
        refine ⟨((hP.eq_iff_even_dist c z u).2
          (by rw [hzu2]; exact ⟨1, by norm_num⟩)).trans hu, ?_⟩
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        omega
  have hdisj : Disjoint (({u} : Finset V) : Set V) (A : Set V) := by
    rw [Set.disjoint_left]
    intro z hz hA
    rw [Finset.mem_coe, Finset.mem_singleton] at hz
    have hA' : z ∈ Finset.univ.filter (fun w => Γ.dist w u = 2) := by
      simpa [A] using hA
    have hdist : Γ.dist z u = 2 := (Finset.mem_filter.mp hA').2
    rw [hz] at hdist
    simp at hdist
  have hAcard : A.card = s * (t + 1) := by
    have hEq : A = Finset.univ.filter (fun z => Γ.dist u z = 2) := by
      ext z
      simp [A, SimpleGraph.dist_comm]
    rw [hEq, card_collinear hP c hdeg hu]
  rw [hset, Set.ncard_union_eq hdisj, Finset.coe_singleton, Set.ncard_singleton,
    Set.ncard_coe_finset, hAcard]
  ring

theorem ncard_of_isOvoid (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {X : Set V}
    (hX : IsOvoid Γ c X) : X.ncard = s * t + 1 := by
  classical
  let P : Finset V := X.toFinset
  let Ls : Finset V := lineFinset c
  let f : V → V := fun L =>
    if h : c L = 1 then (Set.ncard_eq_one.mp (hX.2 L h)).choose else L
  have hf_mem : ∀ L, c L = 1 → f L ∈ X ∧ Γ.Adj L (f L) := by
    intro L hL
    have hset : Γ.neighborSet L ∩ X = {f L} := by
      dsimp only [f]
      rw [dif_pos hL]
      exact (Set.ncard_eq_one.mp (hX.2 L hL)).choose_spec
    have hmem : f L ∈ Γ.neighborSet L ∩ X := by
      rw [hset]
      exact Set.mem_singleton _
    exact ⟨hmem.2, hmem.1⟩
  have hmap : (Ls : Set V).MapsTo f (P : Set V) := by
    intro L hL
    have hL1 : c L = 1 := by simpa [Ls] using (mem_lineFinset.mp hL)
    exact Set.mem_toFinset.mpr (hf_mem L hL1).1
  have hsum := Finset.card_eq_sum_card_fiberwise (s := Ls) (t := P) (f := f) hmap
  have hfiber : ∀ b ∈ P, ({a ∈ Ls | f a = b}).card = t + 1 := by
    intro b hbP
    have hbX : b ∈ X := Set.mem_toFinset.mp (by simpa [P] using hbP)
    have hbc : c b = 0 := hX.1 b hbX
    have hsetEq : {a ∈ Ls | f a = b} = Ls.filter (fun a => Γ.Adj a b) := by
      ext a
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨haL, hfa⟩
        have ha1 : c a = 1 := mem_lineFinset.mp haL
        have hadj : Γ.Adj a (f a) := (hf_mem a ha1).2
        exact ⟨haL, by rwa [hfa] at hadj⟩
      · rintro ⟨haL, hadj⟩
        have ha1 : c a = 1 := mem_lineFinset.mp haL
        have hfaX : f a ∈ X := (hf_mem a ha1).1
        have hfaAdj : Γ.Adj a (f a) := (hf_mem a ha1).2
        have hbIn : b ∈ Γ.neighborSet a ∩ X := ⟨hadj, hbX⟩
        have hfaIn : f a ∈ Γ.neighborSet a ∩ X := ⟨hfaAdj, hfaX⟩
        have hle1 : (Γ.neighborSet a ∩ X).ncard ≤ 1 := le_of_eq (hX.2 a ha1)
        exact ⟨haL, (((Set.ncard_le_one).mp hle1) b hbIn (f a) hfaIn).symm⟩
    have hrow : (Ls.filter (fun a => Γ.Adj a b)).card = t + 1 := by
      have hEq : Ls.filter (fun a => Γ.Adj a b) = Γ.neighborFinset b := by
        ext a
        rw [Finset.mem_filter, mem_lineFinset, mem_neighborFinset]
        constructor
        · rintro ⟨-, h⟩
          exact h.symm
        · intro h
          exact ⟨color_eq_one_of_adj_of_color_eq_zero hbc h, h.symm⟩
      rw [hEq, card_neighborFinset_eq_degree, hdeg b, if_pos hbc]
    rw [hsetEq, hrow]
  have hsum' : Ls.card = P.card * (t + 1) := by
    rw [hsum]
    calc
      ∑ b ∈ P, ({a ∈ Ls | f a = b}).card = ∑ b ∈ P, (t + 1) :=
        Finset.sum_congr rfl hfiber
      _ = P.card * (t + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
  have hline : Ls.card = (t + 1) * (s * t + 1) := by
    simpa [Ls] using card_lineFinset hP hT c hdeg
  have hPcard : P.card = s * t + 1 := by
    have hEq : P.card * (t + 1) = (t + 1) * (s * t + 1) := by
      rw [← hsum', hline]
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos t)
      (by simpa [Nat.mul_comm] using hEq)
  calc
    X.ncard = P.card := by simpa [P] using Set.ncard_eq_toFinset_card' X
    _ = s * t + 1 := hPcard

theorem higman_s_le_t_sq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) : s ≤ t ^ 2 := by
  classical
  let dc : Γ.Coloring (Fin 2) := Γ.recolorOfEquiv (Equiv.swap (0 : Fin 2) 1) c
  have hdc0 : ∀ v, dc v = 0 ↔ c v = 1 := by
    intro v
    change Equiv.swap (0 : Fin 2) 1 (c v) = 0 ↔ c v = 1
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c v) with h | h <;> rw [h] <;> decide
  have hdeg' : ∀ v, Γ.degree v = if dc v = 0 then s + 1 else t + 1 := by
    intro v
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    by_cases hc0 : c v = 0
    · have hdc0' : dc v ≠ 0 := by
        intro h
        have h1 : c v = 1 := (hdc0 v).mp h
        rw [hc0] at h1
        exact absurd h1 (by decide)
      rw [hdeg v, if_pos hc0, if_neg hdc0']
    · have hc1 : c v = 1 := by
        rcases hfin (c v) with h | h
        · exact absurd h hc0
        · exact h
      have hdc0' : dc v = 0 := (hdc0 v).mpr hc1
      rw [hdeg v, if_neg hc0, if_pos hdc0']
  obtain ⟨L, hL⟩ := exists_line hP hT c
  have hdcL : dc L = 0 := (hdc0 L).mpr hL
  have hpos : 0 < (Finset.univ.filter fun y => Γ.dist L y = 4).card := by
    rw [card_opposite hP hT dc hdeg' (x := L) hdcL]
    have ht : 0 < t := by
      have := two_le_t hP hT c hdeg
      omega
    have hs : 0 < s := by
      have := two_le_s hP hT c hdeg
      omega
    exact Nat.mul_pos (pow_pos ht 2) hs
  obtain ⟨M, hM⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hM
  have hLM : Γ.dist L M = 4 := hM.2
  have hLMne : L ≠ M := by
    intro h
    rw [h] at hLM
    simp at hLM
  have hXcard : ({L, M} : Finset V).card = 2 := Finset.card_pair hLMne
  have hsub : (({L, M} : Finset V) : Set V) ⊆ spanSet Γ L M := by
    intro z hz
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact left_mem_spanSet hLM
    · exact right_mem_spanSet hLM
  have hmul := mul_le_sq_of_subset_span hP hT dc hdeg' (x := L) (y := M)
    hdcL hLM hsub (Nat.le_of_eq hXcard.symm)
  simpa [hXcard] using hmul

end Basic

end CFSG.Geometry.GeneralizedQuadrangles

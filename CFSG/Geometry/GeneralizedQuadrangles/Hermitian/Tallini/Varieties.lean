module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Basic
public import CFSG.Geometry.GeneralizedQuadrangles.LinearSpace
public import CFSG.Geometry.GeneralizedQuadrangles.Subquadrangle

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section Elementary

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

@[simp] theorem mem_ptPerp {c : Γ.Coloring (Fin 2)} {X : Set V} {z : V} :
    z ∈ ptPerp Γ c X ↔ c z = 0 ∧ ∀ x ∈ X, Γ.dist z x ≤ 2 := Iff.rfl

@[simp] theorem mem_ptPerp_pair {c : Γ.Coloring (Fin 2)} {x y z : V} :
    z ∈ ptPerp Γ c ({x, y} : Set V) ↔
      c z = 0 ∧ Γ.dist z x ≤ 2 ∧ Γ.dist z y ≤ 2 := by
  rw [mem_ptPerp]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨hz, h x (by simp), h y (by simp)⟩
  · rintro ⟨hz, hx, hy⟩
    refine ⟨hz, ?_⟩
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hx
    · exact hy

theorem mem_starLine_iff {c : Γ.Coloring (Fin 2)} {x y z : V} :
    z ∈ starLine Γ c x y ↔
      c z = 0 ∧ ∀ a, c a = 0 → Γ.dist a x ≤ 2 → Γ.dist a y ≤ 2 → Γ.dist z a ≤ 2 := by
  rw [starLine, mem_ptPerp]
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun a ha hax hay => h a ?_⟩
    rw [mem_ptPerp_pair]
    exact ⟨ha, hax, hay⟩
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun a ha => ?_⟩
    rw [mem_ptPerp_pair] at ha
    exact h a ha.1 ha.2.1 ha.2.2

theorem mem_starLine_left {c : Γ.Coloring (Fin 2)} {x y : V} (hx : c x = 0) :
    x ∈ starLine Γ c x y := by
  rw [mem_starLine_iff]
  refine ⟨hx, fun a _ hax _ => ?_⟩
  simpa [SimpleGraph.dist_comm] using hax

theorem mem_starLine_right {c : Γ.Coloring (Fin 2)} {x y : V} (hy : c y = 0) :
    y ∈ starLine Γ c x y := by
  rw [mem_starLine_iff]
  refine ⟨hy, fun a _ _ hay => ?_⟩
  simpa [SimpleGraph.dist_comm] using hay

theorem starLine_comm {c : Γ.Coloring (Fin 2)} (x y : V) :
    starLine Γ c x y = starLine Γ c y x := by
  unfold starLine
  rw [Set.pair_comm]

theorem color_eq_zero_of_mem_starLine {c : Γ.Coloring (Fin 2)} {x y z : V}
    (hz : z ∈ starLine Γ c x y) : c z = 0 :=
  (mem_starLine_iff.mp hz).1

theorem isStarLine_starLine {c : Γ.Coloring (Fin 2)} {x y : V}
    (hx : c x = 0) (hy : c y = 0) (hxy : x ≠ y) : IsStarLine Γ c (starLine Γ c x y) :=
  ⟨x, y, hx, hy, hxy, rfl⟩

theorem starLine_eq_of_isStarLine_of_mem (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {X : Set V} (hX : IsStarLine Γ c X) {a b : V}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) : X = starLine Γ c a b := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hX
  exact (starLine_eq_of_mem hP hT c hx hy hxy ha hb hab).symm

theorem dist_eq_two_or_four_of_color_zero (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {x y : V} (hx : c x = 0) (hy : c y = 0) (hxy : x ≠ y) :
    Γ.dist x y = 2 ∨ Γ.dist x y = 4 := by
  have heven : Even (Γ.dist x y) := (hP.eq_iff_even_dist c x y).1 (hx.trans hy.symm)
  have hle : Γ.dist x y ≤ 4 := hP.dist_le (by norm_num) x y
  have hne0 : Γ.dist x y ≠ 0 := fun h =>
    hxy ((hP.connected.dist_eq_zero_iff).mp h)
  obtain ⟨k, hk⟩ := heven
  omega

private theorem dist_eq_two_or_four_of_color_eq (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {x y : V} (hc : c x = c y) (hxy : x ≠ y) :
    Γ.dist x y = 2 ∨ Γ.dist x y = 4 := by
  have heven : Even (Γ.dist x y) := (hP.eq_iff_even_dist c x y).1 hc
  have hle : Γ.dist x y ≤ 4 := hP.dist_le (by norm_num) x y
  have hne0 : Γ.dist x y ≠ 0 := fun h => hxy ((hP.connected.dist_eq_zero_iff).mp h)
  obtain ⟨k, hk⟩ := heven
  omega

theorem color_eq_zero_of_dist_eq_two (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {x y : V} (hx : c x = 0) (hxy : Γ.dist x y = 2) : c y = 0 := by
  have h : c x = c y := (hP.eq_iff_even_dist c x y).2 (by rw [hxy]; norm_num)
  rw [← h]
  exact hx

theorem dist_eq_two_of_le_two_of_ne (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {x y : V} (hx : c x = 0) (hy : c y = 0) (hxy : x ≠ y)
    (hle : Γ.dist x y ≤ 2) : Γ.dist x y = 2 := by
  have heven : Even (Γ.dist x y) := (hP.eq_iff_even_dist c x y).1 (hx.trans hy.symm)
  have hne0 : Γ.dist x y ≠ 0 := fun h => hxy ((hP.connected.dist_eq_zero_iff).mp h)
  obtain ⟨k, hk⟩ := heven
  omega

theorem existsUnique_proj_of_not_adj (hP : IsGeneralizedPolygon Γ 4) {c : Γ.Coloring (Fin 2)}
    {x L : V} (hx : c x = 0) (hL : c L = 1) (hxL : ¬ Γ.Adj x L) :
    ∃! u, Γ.Adj L u ∧ Γ.dist x u = 2 := by
  have hdist : Γ.dist x L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hxL (by rw [hx, hL]; norm_num)
  exact existsUnique_proj hP hdist

end Elementary

section VarietiesAStart

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem t_lt_s (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) : t < s := by
  classical
  obtain ⟨⟨x, hx⟩⟩ := hP.exists_point (m := 4) (by norm_num) hT c
  have h3 : 0 < (Γ.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]
    have := hT x
    omega
  obtain ⟨L, hL⟩ := Finset.card_pos.mp h3
  rw [mem_neighborFinset] at hL
  obtain ⟨y, hxy, -⟩ := hP.exists_dist_eq hT hL 4 (by norm_num) (by norm_num)
  let X : Finset V := (spanSet Γ x y).toFinset
  have hXcard : X.card = t + 1 := by
    have h1 : X.card = (spanSet Γ x y).ncard :=
      (Set.ncard_eq_toFinset_card' (spanSet Γ x y)).symm
    rw [h1, hreg x hx y hxy, hdeg x, if_pos hx]
  have hXsub : (X : Set V) ⊆ spanSet Γ x y := by
    intro z hz
    simpa [X] using hz
  have hm : 2 ≤ X.card := by
    have h2 := two_le_t hP hT c hdeg
    rw [hXcard]
    omega
  have hle : t ≤ s :=
    t_le_s_of_card_eq_t_add_one hP hT c hdeg hx hxy hXsub hm hXcard
  omega

theorem isLinearVariety_ptPerp_singleton (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {u : V} (hu : c u = 0) :
    IsLinearVariety Γ c (ptPerp Γ c {u}) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hx y hy hxy
    obtain ⟨hx0, hxu⟩ := hx
    obtain ⟨hy0, hyu⟩ := hy
    intro z hz
    refine ⟨color_eq_zero_of_mem_starLine hz, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    by_cases hxu' : x = u
    · subst x
      have huy : Γ.dist u y = 2 :=
        dist_eq_two_of_le_two_of_ne hP hu hy0 hxy (by simpa [SimpleGraph.dist_comm] using hyu)
      rw [starLine_eq_neighborSet hP hT c hu huy] at hz
      have hzu : Γ.dist z (commonNeighbor hP huy) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr hz.symm
      have hLu : Γ.dist (commonNeighbor hP huy) u = 1 := by
        rw [SimpleGraph.dist_comm]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr (commonNeighbor_adj_left hP huy)
      have htri := hP.connected.dist_triangle (u := z) (v := commonNeighbor hP huy) (w := u)
      omega
    · by_cases hyu' : y = u
      · subst y
        have hux : Γ.dist u x = 2 :=
          dist_eq_two_of_le_two_of_ne hP hu hx0 (Ne.symm hxu')
            (by simpa [SimpleGraph.dist_comm] using hxu)
        rw [starLine_eq_neighborSet hP hT c hx0 (by rw [SimpleGraph.dist_comm]; exact hux)] at hz
        have hzu : Γ.dist z (commonNeighbor hP (by rw [SimpleGraph.dist_comm]; exact hux)) = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr hz.symm
        have hLu :
            Γ.dist (commonNeighbor hP (by rw [SimpleGraph.dist_comm]; exact hux)) u = 1 := by
          rw [SimpleGraph.dist_comm]
          exact SimpleGraph.dist_eq_one_iff_adj.mpr
            (commonNeighbor_adj_right hP (by rw [SimpleGraph.dist_comm]; exact hux))
        have htri := hP.connected.dist_triangle
          (u := z) (v := commonNeighbor hP (by rw [SimpleGraph.dist_comm]; exact hux)) (w := u)
        omega
      · have hux : Γ.dist u x = 2 :=
          dist_eq_two_of_le_two_of_ne hP hu hx0 (Ne.symm hxu')
            (by simpa [SimpleGraph.dist_comm] using hxu)
        have huy : Γ.dist u y = 2 :=
          dist_eq_two_of_le_two_of_ne hP hu hy0 (Ne.symm hyu')
            (by simpa [SimpleGraph.dist_comm] using hyu)
        rcases dist_eq_two_or_four_of_color_zero hP hx0 hy0 hxy with hxy2 | hxy4
        · rw [starLine_eq_neighborSet hP hT c hx0 hxy2] at hz
          obtain ⟨L, ⟨hLx, hLy, hLu⟩, -⟩ :=
            existsUnique_commonNeighbor_of_pairwise_dist_two hP hxy2
              (by rw [SimpleGraph.dist_comm]; exact hux)
              (by rw [SimpleGraph.dist_comm]; exact huy)
          have hL : L = commonNeighbor hP hxy2 :=
            (existsUnique_commonNeighbor hP hxy2).unique
              ⟨hLx, hLy⟩ ⟨commonNeighbor_adj_left hP hxy2,
                commonNeighbor_adj_right hP hxy2⟩
          have hzL : Γ.Adj L z := by rw [hL]; exact hz
          have hzu : Γ.dist z L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hzL.symm
          have huL : Γ.dist L u = 1 := by
            rw [SimpleGraph.dist_comm]
            exact SimpleGraph.dist_eq_one_iff_adj.mpr hLu
          have htri := hP.connected.dist_triangle (u := z) (v := L) (w := u)
          omega
        · rw [starLine_eq_spanSet hP hT c hx0 hxy4] at hz
          have hu_trace : u ∈ traceSet Γ x y :=
            ⟨by rw [SimpleGraph.dist_comm]; exact hux,
              by rw [SimpleGraph.dist_comm]; exact huy⟩
          have hzu : Γ.dist z u ≤ 2 := by
            have h := spanSet_subset_perpSet (x := x) (y := y) (u := u) hu_trace hz
            simpa [mem_perpSet, SimpleGraph.dist_comm] using h
          exact hzu

theorem exists_point_not_mem_ptPerp_singleton (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {u : V} (hu : c u = 0) :
    ∃ w, c w = 0 ∧ w ∉ ptPerp Γ c {u} := by
  classical
  have h3 : 0 < (Γ.neighborFinset u).card := by
    rw [card_neighborFinset_eq_degree]
    have := hT u
    omega
  obtain ⟨L, hL⟩ := Finset.card_pos.mp h3
  rw [mem_neighborFinset] at hL
  obtain ⟨w, huw, -⟩ := hP.exists_dist_eq hT hL 4 (by norm_num) (by norm_num)
  have hcw : c w = 0 := by
    have h : c u = c w := (hP.eq_iff_even_dist c u w).2 (by rw [huw]; exact ⟨2, by norm_num⟩)
    rw [← h]
    exact hu
  refine ⟨w, hcw, ?_⟩
  intro hw
  have hle := hw.2 u (Set.mem_singleton u)
  rw [SimpleGraph.dist_comm, huw] at hle
  omega

theorem isStarPlane_ptPerp_singleton (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {u : V} (hu : c u = 0) :
    IsStarPlane Γ c (ptPerp Γ c {u}) := by
  classical
  have hlin := isLinearVariety_ptPerp_singleton hP hT c hdeg hu
  have hproper := exists_point_not_mem_ptPerp_singleton hP hT c hu
  have h3 : 1 < (Γ.neighborFinset u).card := by
    rw [card_neighborFinset_eq_degree]
    have := hT u
    omega
  obtain ⟨L1, hL1, L2, hL2, hL12⟩ := Finset.one_lt_card.mp h3
  rw [mem_neighborFinset] at hL1 hL2
  have hcL1 : c L1 = 1 := color_eq_one_of_adj_of_color_eq_zero hu hL1
  have hcL2 : c L2 = 1 := color_eq_one_of_adj_of_color_eq_zero hu hL2
  have hpick : ∀ L : V, Γ.Adj u L → ∃ a, a ≠ u ∧ Γ.Adj L a ∧ c a = 0 := by
    intro L hL
    have hcL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hu hL
    have hpos : 0 < ((Γ.neighborFinset L).erase u).card := by
      rw [Finset.card_erase_of_mem (by simpa [mem_neighborFinset] using hL.symm),
        card_neighborFinset_eq_degree, degree_eq_s_add_one_of_color_one hdeg hcL]
      have := two_le_s hP hT c hdeg
      omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_erase, mem_neighborFinset] at ha
    have hca : c a = 0 := by
      have hne := c.valid ha.2
      have hfin : ∀ z : Fin 2, z = 0 ∨ z = 1 := by decide
      rcases hfin (c a) with h | h
      · exact h
      · exact absurd (hcL.trans h.symm) hne
    exact ⟨a, ha.1, ha.2, hca⟩
  obtain ⟨a1, ha1u, ha1L, ha1c⟩ := hpick L1 hL1
  obtain ⟨a2, ha2u, ha2L, ha2c⟩ := hpick L2 hL2
  have hua1 : Γ.dist u a1 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hL1 ha1L ha1u.symm
  have hua2 : Γ.dist u a2 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hL2 ha2L ha2u.symm
  have hu_mem : u ∈ ptPerp Γ c {u} := by
    rw [mem_ptPerp]
    refine ⟨hu, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simp
  have ha1_mem : a1 ∈ ptPerp Γ c {u} := by
    rw [mem_ptPerp]
    refine ⟨ha1c, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simpa [SimpleGraph.dist_comm] using le_of_eq hua1
  have ha2_mem : a2 ∈ ptPerp Γ c {u} := by
    rw [mem_ptPerp]
    refine ⟨ha2c, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simpa [SimpleGraph.dist_comm] using le_of_eq hua2
  have hnc : ¬ IsStarCollinear Γ c u a1 a2 := by
    rintro ⟨X, hX, huX, ha1X, ha2X⟩
    have hX1 : X = starLine Γ c u a1 :=
      starLine_eq_of_isStarLine_of_mem hP hT hX huX ha1X (Ne.symm ha1u)
    have hX2 : X = starLine Γ c u a2 :=
      starLine_eq_of_isStarLine_of_mem hP hT hX huX ha2X (Ne.symm ha2u)
    have heq : starLine Γ c u a1 = starLine Γ c u a2 := hX1.symm.trans hX2
    rw [starLine_eq_neighborSet hP hT c hu hua1,
      starLine_eq_neighborSet hP hT c hu hua2] at heq
    have hL1eq : L1 = commonNeighbor hP hua1 := eq_commonNeighbor hP hua1 hL1 ha1L.symm
    have hL2eq : L2 = commonNeighbor hP hua2 := eq_commonNeighbor hP hua2 hL2 ha2L.symm
    rw [← hL1eq, ← hL2eq] at heq
    have ha1L2 : Γ.Adj L2 a1 := by
      have h : a1 ∈ Γ.neighborSet L1 := ha1L
      rwa [heq] at h
    have huniq := (existsUnique_commonNeighbor hP hua1).unique
      ⟨hL1, ha1L.symm⟩ ⟨hL2, ha1L2.symm⟩
    exact hL12 huniq
  exact ⟨⟨hlin, hproper⟩, u, hu_mem, a1, ha1_mem, a2, ha2_mem, hnc⟩

private theorem exists_mem_neighborSet_of_opposite_lines (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {L M : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4) {v : V}
    (hv : Γ.Adj L v) : ∃ m, Γ.Adj M m ∧ Γ.dist v m = 2 := by
  classical
  have hLM_ne : L ≠ M := by
    rintro rfl
    simp at hLM
  have hnot : ∀ m ∈ Γ.neighborSet M, ¬ Γ.Adj L m := by
    intro m hm hLm
    have hMm : Γ.Adj m M := hm.symm
    have h2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hLm hMm hLM_ne
    omega
  have hnot' : ∀ m ∈ Γ.neighborSet M, ¬ Γ.Adj m L := fun m hm h => hnot m hm h.symm
  let f : ↥(Γ.neighborSet M) → V := fun m =>
    proj hP (dist_eq_three_of_not_adj_of_color_ne hP c (hnot' m.1 m.2)
      (by rw [color_eq_zero_of_adj_of_color_eq_one hM m.2, hL]; norm_num))
  have hfadj : ∀ m : ↥(Γ.neighborSet M), Γ.Adj L (f m) := fun m =>
    proj_adj hP (dist_eq_three_of_not_adj_of_color_ne hP c (hnot' m.1 m.2)
      (by rw [color_eq_zero_of_adj_of_color_eq_one hM m.2, hL]; norm_num))
  have hfdist : ∀ m : ↥(Γ.neighborSet M), Γ.dist m.1 (f m) = 2 := fun m =>
    proj_dist hP (dist_eq_three_of_not_adj_of_color_ne hP c (hnot' m.1 m.2)
      (by rw [color_eq_zero_of_adj_of_color_eq_one hM m.2, hL]; norm_num))
  have hfinj : Function.Injective f := by
    intro m m' hmm'
    apply Subtype.ext
    have hfM : ¬ Γ.Adj (f m) M := by
      intro hMf
      have h2 : Γ.dist L M = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP (hfadj m) hMf hLM_ne
      omega
    have haz : Γ.dist (f m) m.1 = 2 := by
      rw [SimpleGraph.dist_comm]
      exact hfdist m
    have hau : Γ.dist (f m) m'.1 = 2 := by
      rw [SimpleGraph.dist_comm, hmm']
      exact hfdist m'
    exact eq_of_adj_of_dist_two_of_not_adj (hP := hP) (c := c) hfM m.2 m'.2 haz hau
  have himg : (Set.range f).ncard = (Γ.neighborSet M).ncard := by
    rw [Set.ncard_range_of_injective hfinj, Nat.card_coe_set_eq]
  have hsub : Set.range f ⊆ Γ.neighborSet L := by
    rintro z ⟨m, rfl⟩
    exact hfadj m
  have hcardM : (Γ.neighborSet M).ncard = s + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg M, if_neg (by rw [hM]; decide)]
  have hcardL : (Γ.neighborSet L).ncard = s + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg L, if_neg (by rw [hL]; decide)]
  have hrange : Set.range f = Γ.neighborSet L := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [hcardL, himg, hcardM]
  have hvrange : v ∈ Set.range f := by
    rw [hrange]
    exact hv
  obtain ⟨m, hm⟩ := hvrange
  refine ⟨m.1, m.2, ?_⟩
  rw [← hm]
  simpa [SimpleGraph.dist_comm] using hfdist m

private theorem exists_line_through_ne (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {u L : V} (hu : c u = 0) (huL : Γ.Adj u L) : ∃ N, Γ.Adj u N ∧ N ≠ L := by
  classical
  have h3 : 0 < ((Γ.neighborFinset u).erase L).card := by
    rw [Finset.card_erase_of_mem (by simpa [mem_neighborFinset] using huL),
      card_neighborFinset_eq_degree, hdeg u, if_pos hu]
    have := two_le_t hP hT c hdeg
    omega
  obtain ⟨N, hN⟩ := Finset.card_pos.mp h3
  rw [Finset.mem_erase, mem_neighborFinset] at hN
  exact ⟨N, hN.2, hN.1⟩

private theorem exists_point_on_line_ne (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {L u : V} (hL : c L = 1) (huL : Γ.Adj L u) : ∃ a, Γ.Adj L a ∧ a ≠ u := by
  classical
  have h3 : 0 < ((Γ.neighborFinset L).erase u).card := by
    rw [Finset.card_erase_of_mem (by simpa [mem_neighborFinset] using huL),
      card_neighborFinset_eq_degree, hdeg L, if_neg (by rw [hL]; decide)]
    have := two_le_s hP hT c hdeg
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp h3
  rw [Finset.mem_erase, mem_neighborFinset] at ha
  exact ⟨a, ha.2, ha.1⟩

private theorem adj_of_pairwise_dist_two_of_adj_adj (hP : IsGeneralizedPolygon Γ 4)
    {p q r L : V} (hpq : Γ.dist p q = 2) (hpr : Γ.dist p r = 2)
    (hqr : Γ.dist q r = 2) (hLq : Γ.Adj L q) (hLr : Γ.Adj L r) (hqr_ne : q ≠ r) :
    Γ.Adj L p := by
  obtain ⟨N, ⟨hpN, hqN, hrN⟩, -⟩ :=
    existsUnique_commonNeighbor_of_pairwise_dist_two hP hpq hpr hqr
  have hLN : L = N :=
    (existsUnique_commonNeighbor hP hqr).unique ⟨hLq.symm, hLr.symm⟩ ⟨hqN, hrN⟩
  rw [hLN]
  exact hpN.symm

theorem ptPerp_subset_of_isLinearVariety (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsLinearVariety Γ c X)
    {L x u : V} (hL : c L = 1) (hLX : Γ.neighborSet L ⊆ X) (hx : x ∈ X) (hxL : ¬ Γ.Adj L x)
    (huL : Γ.Adj L u) (hxu : Γ.dist x u = 2) : ptPerp Γ c {u} ⊆ X := by
  classical
  have hx0 : c x = 0 := hX.1 x hx
  have hu0 : c u = 0 := by
    have hne := c.valid huL
    have hfin : ∀ z : Fin 2, z = 0 ∨ z = 1 := by decide
    rcases hfin (c u) with h | h
    · exact h
    · exact absurd (hL.trans h.symm) hne
  have huX : u ∈ X := hLX huL
  have hxu_ne : x ≠ u := by
    rintro rfl
    simp at hxu
  have hLpos : 0 < ((Γ.neighborFinset L).erase u).card := by
    rw [Finset.card_erase_of_mem (by simpa [mem_neighborFinset] using huL),
      card_neighborFinset_eq_degree, hdeg L, if_neg (by rw [hL]; decide)]
    have := two_le_s hP hT c hdeg
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hLpos
  rw [Finset.mem_erase, mem_neighborFinset] at hy
  have hyX : y ∈ X := hLX hy.2
  have huy : Γ.dist u y = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP huL.symm hy.2 hy.1.symm
  have hux : Γ.dist u x = 2 := by rw [SimpleGraph.dist_comm]; exact hxu
  have hcy : commonNeighbor hP huy = L :=
    (eq_commonNeighbor hP huy huL.symm hy.2.symm).symm
  have hne : commonNeighbor hP hux ≠ commonNeighbor hP huy := by
    rw [hcy]
    intro h
    exact hxL (h ▸ (commonNeighbor_adj_right hP hux).symm)
  have hxy4 : Γ.dist x y = 4 :=
    dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP hux huy hne
  have hxy_ne : x ≠ y := by
    rintro rfl
    simp at hxy4
  let S : Set V := spanSet Γ x y
  have hSsubX : S ⊆ X := by
    intro z hz
    exact hX.2 x hx y hyX hxy_ne (by
      rw [starLine_eq_spanSet hP hT c hx0 hxy4]
      exact hz)
  have hu_trace : u ∈ traceSet Γ x y :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hux,
      by rw [SimpleGraph.dist_comm]; exact huy⟩
  have hdistS : ∀ z ∈ S, Γ.dist z u = 2 := fun z hz =>
    dist_eq_two_of_mem_span_of_mem_trace hP hT hxy4 hz hu_trace
  have hScard : S.ncard = t + 1 := by
    change (spanSet Γ x y).ncard = t + 1
    rw [hreg x hx0 y hxy4, hdeg x, if_pos hx0]
  let φ : S → V := fun z => commonNeighbor hP (hdistS z.1 z.2)
  have hinj : Function.Injective φ := by
    intro z z' hzz'
    apply Subtype.ext
    by_contra hne
    have h4 : Γ.dist z.1 z'.1 = 4 :=
      dist_eq_four_of_mem_span hP hT hxy4 z.2 z'.2 hne
    have hzφ : Γ.Adj z.1 (φ z) := commonNeighbor_adj_left hP (hdistS z.1 z.2)
    have hz'φ : Γ.Adj (φ z) z'.1 := by
      have h : Γ.Adj z'.1 (φ z') := commonNeighbor_adj_left hP (hdistS z'.1 z'.2)
      rw [← hzz'] at h
      exact h.symm
    have h2 : Γ.dist z.1 z'.1 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hzφ hz'φ hne
    omega
  have hImcard : (Set.range φ).ncard = S.ncard := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_coe_set_eq]
  have hImsub : Set.range φ ⊆ Γ.neighborSet u := by
    rintro z ⟨z₀, rfl⟩
    exact commonNeighbor_adj_right hP (hdistS z₀.1 z₀.2)
  have huNcard : (Γ.neighborSet u).ncard = t + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg u, if_pos hu0]
  have hImEq : Set.range φ = Γ.neighborSet u := by
    refine Set.eq_of_subset_of_ncard_le hImsub ?_
    rw [huNcard, hImcard, hScard]
  intro w hw
  obtain ⟨hw0, hwu⟩ := hw
  by_cases hwu_eq : w = u
  · rw [hwu_eq]
    exact huX
  · have huw : Γ.dist u w = 2 :=
      dist_eq_two_of_le_two_of_ne hP hu0 hw0 (Ne.symm hwu_eq)
        (by simpa [SimpleGraph.dist_comm] using hwu)
    let N : V := commonNeighbor hP huw
    have hNmem : N ∈ Γ.neighborSet u := commonNeighbor_adj_left hP huw
    have hNrange : N ∈ Set.range φ := by
      rw [hImEq]
      exact hNmem
    obtain ⟨z, hzN⟩ := hNrange
    have hzX : z.1 ∈ X := hSsubX z.2
    have hz0 : c z.1 = 0 := hX.1 z.1 hzX
    have hzu : Γ.dist z.1 u = 2 := hdistS z.1 z.2
    have hz_ne_u : z.1 ≠ u := by
      intro h
      exact (not_mem_spanSet_of_mem_traceSet hP hT hxy4 hu_trace) (h ▸ z.2)
    have hw_star : w ∈ starLine Γ c z.1 u := by
      rw [starLine_eq_neighborSet hP hT c hz0 hzu]
      change Γ.Adj (φ z) w
      rw [hzN]
      exact (commonNeighbor_adj_right hP huw).symm
    exact hX.2 z.1 hzX u huX hz_ne_u hw_star

theorem eq_ptPerp_of_isProperVariety (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsProperVariety Γ c X)
    {L x u : V} (hL : c L = 1) (hLX : Γ.neighborSet L ⊆ X) (hx : x ∈ X) (hxL : ¬ Γ.Adj L x)
    (huL : Γ.Adj L u) (hxu : Γ.dist x u = 2) : X = ptPerp Γ c {u} := by
  classical
  have hlin : IsLinearVariety Γ c X := hX.1
  have hx0 : c x = 0 := hlin.1 x hx
  have hu0 : c u = 0 := color_eq_zero_of_dist_eq_two hP hx0 hxu
  have hperp_u : ptPerp Γ c {u} ⊆ X :=
    ptPerp_subset_of_isLinearVariety hP hT c hdeg hreg hlin hL hLX hx hxL huL hxu
  refine Set.Subset.antisymm ?_ hperp_u
  intro w hwX
  by_contra hwperp
  have hw0 : c w = 0 := hlin.1 w hwX
  have hw_not_u : w ≠ u := by
    intro h
    apply hwperp
    rw [h]
    rw [mem_ptPerp]
    refine ⟨hu0, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    simp
  have hw_gt : 2 < Γ.dist w u := by
    have hle : ¬ Γ.dist w u ≤ 2 := fun hle => hwperp (by
      rw [mem_ptPerp]
      refine ⟨hw0, ?_⟩
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      exact hle)
    omega
  have hw4 : Γ.dist w u = 4 := by
    rcases dist_eq_two_or_four_of_color_zero hP hw0 hu0 hw_not_u with h2 | h4
    · omega
    · exact h4
  have hw_not_L : ¬ Γ.Adj L w := by
    intro hLw
    have h2 : Γ.dist w u = 2 := dist_eq_two_of_adj_of_adj_of_ne hP hLw.symm huL hw_not_u
    omega
  have hwL3 : Γ.dist w L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hw_not_L h.symm)
      (by rw [hw0, hL]; norm_num)
  let w' := proj hP hwL3
  have hw'L : Γ.Adj L w' := proj_adj hP hwL3
  have hww' : Γ.dist w w' = 2 := proj_dist hP hwL3
  have hw'_ne_u : w' ≠ u := by
    intro h
    have h2 : Γ.dist w u = 2 := by simpa [h] using hww'
    omega
  have hperp_w' : ptPerp Γ c {w'} ⊆ X :=
    ptPerp_subset_of_isLinearVariety hP hT c hdeg hreg hlin hL hLX hwX hw_not_L hw'L hww'
  obtain ⟨Nu, hNuL, hNu_ne⟩ := exists_line_through_ne hP hT c hdeg hu0 huL.symm
  have hcNu : c Nu = 1 := color_eq_one_of_adj_of_color_eq_zero hu0 hNuL
  obtain ⟨a, haNu, ha_ne_u⟩ :=
    exists_point_on_line_ne hP hT c hdeg hcNu hNuL.symm
  have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hcNu haNu
  have hau : Γ.dist a u = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP haNu.symm hNuL.symm ha_ne_u
  have ha_perp : a ∈ ptPerp Γ c {u} := by
    rw [mem_ptPerp]
    refine ⟨ha0, ?_⟩
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst b
    exact le_of_eq hau
  have haX : a ∈ X := hperp_u ha_perp
  have ha_not_L : ¬ Γ.Adj L a := by
    intro hLa
    have hLNu : L = Nu :=
      (existsUnique_commonNeighbor hP hau).unique
        ⟨hLa.symm, huL.symm⟩ ⟨haNu.symm, hNuL⟩
    exact hNu_ne hLNu.symm
  have hw'0 : c w' = 0 := color_eq_zero_of_adj_of_color_eq_one hL hw'L
  obtain ⟨N', hN'w', hN'_ne⟩ :=
    exists_line_through_ne hP hT c hdeg hw'0 hw'L.symm
  have hcN' : c N' = 1 := color_eq_one_of_adj_of_color_eq_zero hw'0 hN'w'
  have ha_ne_w' : a ≠ w' := by
    intro h
    apply ha_not_L
    rw [h]
    exact hw'L
  have huw' : Γ.dist u w' = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP huL.symm hw'L (Ne.symm hw'_ne_u)
  have ha_not_N' : ¬ Γ.Adj N' a := by
    intro hN'a
    have haw' : Γ.dist a w' = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hN'a.symm hN'w'.symm ha_ne_w'
    have hLa : Γ.Adj L a :=
      adj_of_pairwise_dist_two_of_adj_adj hP hau haw' huw' huL hw'L (Ne.symm hw'_ne_u)
    exact ha_not_L hLa
  have haN'3 : Γ.dist a N' = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c (fun h => ha_not_N' h.symm)
      (by rw [ha0, hcN']; norm_num)
  let b := proj hP haN'3
  have hbN' : Γ.Adj N' b := proj_adj hP haN'3
  have hab : Γ.dist a b = 2 := proj_dist hP haN'3
  have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hcN' hbN'
  have hb_ne_w' : b ≠ w' := by
    intro hbw
    have haw' : Γ.dist a w' = 2 := by
      rw [hbw] at hab
      exact hab
    have hLa : Γ.Adj L a :=
      adj_of_pairwise_dist_two_of_adj_adj hP hau haw' huw' huL hw'L (Ne.symm hw'_ne_u)
    exact ha_not_L hLa
  have hbw' : Γ.dist b w' = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hbN'.symm hN'w'.symm hb_ne_w'
  have hb_perp : b ∈ ptPerp Γ c {w'} := by
    rw [mem_ptPerp]
    refine ⟨hb0, ?_⟩
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact le_of_eq hbw'
  have hbX : b ∈ X := hperp_w' hb_perp
  have hab_ne : a ≠ b := by
    intro h
    rw [h] at hab
    simp at hab
  let M : Set V := starLine Γ c a b
  let NM : V := commonNeighbor hP hab
  have hNM_line : c NM = 1 :=
    color_eq_one_of_adj_of_color_eq_zero ha0 (commonNeighbor_adj_left hP hab)
  have hM_eq : M = Γ.neighborSet NM := starLine_eq_neighborSet hP hT c ha0 hab
  have hM_subX : M ⊆ X := by
    intro z hz
    exact hlin.2 a haX b hbX hab_ne hz
  have haM : Γ.Adj NM a := by
    have h : a ∈ Γ.neighborSet NM := by
      rw [← hM_eq]
      exact mem_starLine_left ha0
    exact h
  have hbM : Γ.Adj NM b := by
    have h : b ∈ Γ.neighborSet NM := by
      rw [← hM_eq]
      exact mem_starLine_right hb0
    exact h
  have hNM_ne_L : NM ≠ L := by
    intro h
    apply ha_not_L
    rw [h] at haM
    exact haM
  have hb_not_L : ¬ Γ.Adj L b := by
    intro hLb
    have hN'L : N' = L :=
      eq_of_two_common_points hP hb_ne_w' hbN' hN'w'.symm hLb hw'L
    exact hN'_ne hN'L
  have hno_common : ∀ v, ¬ (Γ.Adj L v ∧ Γ.Adj NM v) := by
    intro v hv
    obtain ⟨hLv, hNMv⟩ := hv
    have hva : Γ.dist v a = 2 := by
      have hne : v ≠ a := by
        intro h
        apply ha_not_L
        rw [← h]
        exact hLv
      exact dist_eq_two_of_adj_of_adj_of_ne hP hNMv.symm haM hne
    have hvb : Γ.dist v b = 2 := by
      have hne : v ≠ b := by
        intro h
        apply hb_not_L
        rw [← h]
        exact hLv
      exact dist_eq_two_of_adj_of_adj_of_ne hP hNMv.symm hbM hne
    by_cases hvu : v = u
    · subst v
      have hbu_ne : b ≠ u := by
        intro h
        apply hb_not_L
        rwa [h]
      have hbu : Γ.dist b u = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hbM.symm hNMv hbu_ne
      have hLb : Γ.Adj L b :=
        adj_of_pairwise_dist_two_of_adj_adj hP hbu hbw' huw' huL hw'L
          (Ne.symm hw'_ne_u)
      exact hb_not_L hLb
    · have huv : Γ.dist u v = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP huL.symm hLv (Ne.symm hvu)
      have hLv' : Γ.Adj L a :=
        adj_of_pairwise_dist_two_of_adj_adj hP hau
          (by rw [SimpleGraph.dist_comm]; exact hva) huv huL hLv (Ne.symm hvu)
      exact ha_not_L hLv'
  have hdist2 : Γ.dist L NM ≠ 2 := by
    intro h2
    obtain ⟨v, ⟨hLv, hNMv⟩, -⟩ := existsUnique_commonNeighbor hP h2
    exact hno_common v ⟨hLv, hNMv⟩
  have hdist4 : Γ.dist L NM = 4 := by
    rcases dist_eq_two_or_four_of_color_eq hP (by rw [hL, hNM_line]) (Ne.symm hNM_ne_L)
      with h2 | h4
    · exact absurd h2 hdist2
    · exact h4
  have hperp_of_mem_L : ∀ v, Γ.Adj L v → ptPerp Γ c {v} ⊆ X := by
    intro v hLv
    obtain ⟨m, hNMm, hvm⟩ :=
      exists_mem_neighborSet_of_opposite_lines hP hT c hdeg hL hNM_line hdist4 hLv
    have hmM : m ∈ M := by
      rw [hM_eq]
      exact hNMm
    have hmX : m ∈ X := hM_subX hmM
    have hm_not_L : ¬ Γ.Adj L m := by
      intro hLm
      exact hno_common m ⟨hLm, hNMm⟩
    exact ptPerp_subset_of_isLinearVariety hP hT c hdeg hreg hlin hL hLX hmX hm_not_L
      hLv (by rw [SimpleGraph.dist_comm]; exact hvm)
  obtain ⟨w0, hw00, hw0_notX⟩ := hX.2
  by_cases hLw0 : Γ.Adj L w0
  · exact hw0_notX (hLX hLw0)
  · have hw0L3 : Γ.dist w0 L = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hLw0 h.symm)
        (by rw [hw00, hL]; norm_num)
    let v := proj hP hw0L3
    have hvL : Γ.Adj L v := proj_adj hP hw0L3
    have hw0v : Γ.dist w0 v = 2 := proj_dist hP hw0L3
    have hv_perp : w0 ∈ ptPerp Γ c {v} := by
      rw [mem_ptPerp]
      refine ⟨hw00, ?_⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact le_of_eq hw0v
    exact hw0_notX (hperp_of_mem_L v hvL hv_perp)

end VarietiesAStart

end CFSG.Geometry.GeneralizedQuadrangles

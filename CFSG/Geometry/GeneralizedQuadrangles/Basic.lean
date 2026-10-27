module

public import CFSG.Geometry.GeneralizedPolygons.PointGraph
public import CFSG.Geometry.GeneralizedPolygons.Valency
public import CFSG.Quasithin.Background.F3Paths
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph

universe u

variable {V : Type u}

section Vocabulary

variable (Γ : SimpleGraph V)

@[expose] def perpSet (x : V) : Set V := {y | Γ.dist x y ≤ 2}

@[expose] def traceSet (x y : V) : Set V := {w | Γ.dist x w = 2 ∧ Γ.dist y w = 2}

@[expose] def spanSet (x y : V) : Set V := {z | ∀ w ∈ traceSet Γ x y, Γ.dist z w ≤ 2}

@[expose] def clSet (x y : V) : Set V := {z | ∃ w ∈ spanSet Γ x y, Γ.dist z w ≤ 2}

@[expose] def IsRegularVertex [Fintype V] [DecidableRel Γ.Adj] (x : V) : Prop :=
  ∀ y, Γ.dist x y = 4 → (spanSet Γ x y).ncard = Γ.degree x

@[expose] def HasPropertyH (u : V) : Prop :=
  ∀ x y z, Γ.dist u x = 2 → Γ.dist u y = 2 → Γ.dist u z = 2 →
    Γ.dist x y = 4 → Γ.dist y z = 4 → Γ.dist x z = 4 →
    (z ∈ clSet Γ x y ↔ x ∈ clSet Γ y z)

@[simp] theorem mem_perpSet {x y : V} : y ∈ perpSet Γ x ↔ Γ.dist x y ≤ 2 := Iff.rfl

@[simp] theorem mem_traceSet {x y w : V} :
    w ∈ traceSet Γ x y ↔ Γ.dist x w = 2 ∧ Γ.dist y w = 2 := Iff.rfl

@[simp] theorem mem_spanSet {x y z : V} :
    z ∈ spanSet Γ x y ↔ ∀ w ∈ traceSet Γ x y, Γ.dist z w ≤ 2 := Iff.rfl

@[simp] theorem mem_clSet {x y z : V} :
    z ∈ clSet Γ x y ↔ ∃ w ∈ spanSet Γ x y, Γ.dist z w ≤ 2 := Iff.rfl

end Vocabulary

section Groups

variable (H : Type*) [Group H] [MulAction H V]

@[expose] def rootGroup (Γ : SimpleGraph V) (a b c : V) : Subgroup H :=
  fixingSubgroup H (Γ.neighborSet a) ⊓ fixingSubgroup H (Γ.neighborSet b) ⊓
    fixingSubgroup H (Γ.neighborSet c)

@[expose] def whorlGroup (Γ : SimpleGraph V) (v : V) : Subgroup H :=
  fixingSubgroup H (Γ.neighborSet v)

@[expose] def symmetryGroup (Γ : SimpleGraph V) (v : V) : Subgroup H :=
  fixingSubgroup H (perpSet Γ v)

@[simp] theorem mem_rootGroup {Γ : SimpleGraph V} {a b c : V} {g : H} :
    g ∈ rootGroup H Γ a b c ↔
      g ∈ fixingSubgroup H (Γ.neighborSet a) ∧
        g ∈ fixingSubgroup H (Γ.neighborSet b) ∧
          g ∈ fixingSubgroup H (Γ.neighborSet c) := by
  simp [rootGroup, and_assoc]

@[simp] theorem mem_whorlGroup {Γ : SimpleGraph V} {v : V} {g : H} :
    g ∈ whorlGroup H Γ v ↔ g ∈ fixingSubgroup H (Γ.neighborSet v) := Iff.rfl

@[simp] theorem mem_symmetryGroup {Γ : SimpleGraph V} {v : V} {g : H} :
    g ∈ symmetryGroup H Γ v ↔ g ∈ fixingSubgroup H (perpSet Γ v) := Iff.rfl

end Groups

end CFSG.Geometry.GeneralizedQuadrangles

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin

universe u

variable {V : Type u}

section Basics

variable {Γ : SimpleGraph V}

theorem existsUnique_proj (hP : IsGeneralizedPolygon Γ 4) {x L : V}
    (h : Γ.dist x L = 3) : ∃! w, Γ.Adj L w ∧ Γ.dist x w = 2 := by
  obtain ⟨w, hLw, hxw⟩ := hP.exists_adj_dist_succ (y := x) (v := L) (by rw [h]; norm_num)
  have hxw' : Γ.dist x w = 2 := by omega
  refine ⟨w, ⟨hLw, hxw'⟩, fun w' hw' => ?_⟩
  exact (hP.eq_of_adj_of_dist_succ (y := x) (v := L) (by rw [h]; norm_num)
    hLw hw'.1 (by omega) (by omega)).symm

@[expose] noncomputable def proj (hP : IsGeneralizedPolygon Γ 4) {x L : V}
    (h : Γ.dist x L = 3) : V :=
  (existsUnique_proj hP h).choose

theorem proj_adj (hP : IsGeneralizedPolygon Γ 4) {x L : V} (h : Γ.dist x L = 3) :
    Γ.Adj L (proj hP h) :=
  (existsUnique_proj hP h).choose_spec.1.1

theorem proj_dist (hP : IsGeneralizedPolygon Γ 4) {x L : V} (h : Γ.dist x L = 3) :
    Γ.dist x (proj hP h) = 2 :=
  (existsUnique_proj hP h).choose_spec.1.2

theorem eq_proj (hP : IsGeneralizedPolygon Γ 4) {x L w : V} (h : Γ.dist x L = 3)
    (hLw : Γ.Adj L w) (hxw : Γ.dist x w = 2) : w = proj hP h :=
  (existsUnique_proj hP h).choose_spec.2 w ⟨hLw, hxw⟩

theorem existsUnique_commonNeighbor (hP : IsGeneralizedPolygon Γ 4) {x y : V}
    (h : Γ.dist x y = 2) : ∃! w, Γ.Adj x w ∧ Γ.Adj y w := by
  have hyx : Γ.dist y x = 2 := by rw [dist_comm]; exact h
  obtain ⟨w, hxw, hyw⟩ := hP.exists_adj_dist_succ (y := y) (v := x) (by rw [hyx]; norm_num)
  have hyw' : Γ.Adj y w := by
    have hd : Γ.dist y w = 1 := by omega
    exact SimpleGraph.dist_eq_one_iff_adj.mp hd
  refine ⟨w, ⟨hxw, hyw'⟩, fun w' hw' => ?_⟩
  have hd1 : Γ.dist y w + 1 = Γ.dist y x := by
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hyw', hyx]
  have hd2 : Γ.dist y w' + 1 = Γ.dist y x := by
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hw'.2, hyx]
  exact (hP.eq_of_adj_of_dist_succ (y := y) (v := x) (by rw [hyx]; norm_num)
    hxw hw'.1 hd1 hd2).symm

@[expose] noncomputable def commonNeighbor (hP : IsGeneralizedPolygon Γ 4) {x y : V}
    (h : Γ.dist x y = 2) : V :=
  (existsUnique_commonNeighbor hP h).choose

theorem commonNeighbor_adj_left (hP : IsGeneralizedPolygon Γ 4) {x y : V}
    (h : Γ.dist x y = 2) : Γ.Adj x (commonNeighbor hP h) :=
  (existsUnique_commonNeighbor hP h).choose_spec.1.1

theorem commonNeighbor_adj_right (hP : IsGeneralizedPolygon Γ 4) {x y : V}
    (h : Γ.dist x y = 2) : Γ.Adj y (commonNeighbor hP h) :=
  (existsUnique_commonNeighbor hP h).choose_spec.1.2

theorem eq_commonNeighbor (hP : IsGeneralizedPolygon Γ 4) {x y w : V} (h : Γ.dist x y = 2)
    (hxw : Γ.Adj x w) (hyw : Γ.Adj y w) : w = commonNeighbor hP h :=
  (existsUnique_commonNeighbor hP h).choose_spec.2 w ⟨hxw, hyw⟩

theorem existsUnique_commonNeighbor_of_pairwise_dist_two (hP : IsGeneralizedPolygon Γ 4)
    {x y z : V} (hxy : Γ.dist x y = 2) (hxz : Γ.dist x z = 2) (hyz : Γ.dist y z = 2) :
    ∃! w, Γ.Adj x w ∧ Γ.Adj y w ∧ Γ.Adj z w := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_commonNeighbor hP hxy
  have hzu : Γ.Adj z u := by
    by_contra hzu
    have hzx : Γ.dist z x = 2 := by rw [dist_comm]; exact hxz
    have hzy : Γ.dist z y = 2 := by rw [dist_comm]; exact hyz
    have hzu3 : Γ.dist z u = 3 := by
      rcases hP.dist_adj hu.1.symm z with h | h
      · exfalso
        exact hzu (SimpleGraph.dist_eq_one_iff_adj.mp (by omega))
      · omega
    have hxy' : x = y := (existsUnique_proj hP hzu3).unique
      ⟨hu.1.symm, hzx⟩ ⟨hu.2.symm, hzy⟩
    have : Γ.dist x y = 0 := by rw [hxy']; exact SimpleGraph.dist_self
    omega
  exact ⟨u, ⟨hu.1, hu.2, hzu⟩, fun w hw => huniq w ⟨hw.1, hw.2.1⟩⟩

end Basics

section TraceAndSpan

variable {Γ : SimpleGraph V}

theorem dist_eq_three_of_adj_of_dist_eq_four (hP : IsGeneralizedPolygon Γ 4) {x y L : V}
    (hxy : Γ.dist x y = 4) (hL : Γ.Adj x L) : Γ.dist y L = 3 := by
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  have hyx : Γ.dist y x = 4 := by rw [dist_comm]; exact hxy
  rcases hP.dist_adj hL y with h | h
  · rw [hyx] at h
    have := hP.dist_le h4 y L
    omega
  · rw [hyx] at h
    omega

theorem ncard_trace [Fintype V] [DecidableRel Γ.Adj] (hP : IsGeneralizedPolygon Γ 4)
    {x y : V} (hxy : Γ.dist x y = 4) :
    (traceSet Γ x y).ncard = Γ.degree x := by
  classical
  let f : ↥(Γ.neighborSet x) → ↥(traceSet Γ x y) := fun L =>
    ⟨proj hP (dist_eq_three_of_adj_of_dist_eq_four hP hxy L.2), by
      refine ⟨?_, proj_dist hP (dist_eq_three_of_adj_of_dist_eq_four hP hxy L.2)⟩
      have hAdj : Γ.Adj L.1 (proj hP (dist_eq_three_of_adj_of_dist_eq_four hP hxy L.2)) :=
        proj_adj hP (dist_eq_three_of_adj_of_dist_eq_four hP hxy L.2)
      have hxL : Γ.dist x L.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr L.2
      rcases hP.dist_adj hAdj x with h | h
      · omega
      · exfalso
        have hxw : Γ.dist x (proj hP (dist_eq_three_of_adj_of_dist_eq_four hP hxy L.2)) = 0 := by
          omega
        have hxw' : x = proj hP (dist_eq_three_of_adj_of_dist_eq_four hP hxy L.2) :=
          (hP.connected.dist_eq_zero_iff).mp hxw
        have h2 : Γ.dist y x = 2 := by
          simpa [hxw'] using proj_dist hP (dist_eq_three_of_adj_of_dist_eq_four hP hxy L.2)
        have h4 : Γ.dist y x = 4 := by rw [dist_comm]; exact hxy
        omega⟩
  have hinj : Function.Injective f := by
    intro L L' hLL'
    have hw : (f L).1 = (f L').1 := congrArg Subtype.val hLL'
    have hxw : Γ.dist x (f L).1 = 2 := (f L).2.1
    have hLc : Γ.Adj x L.1 ∧ Γ.Adj (f L).1 L.1 :=
      ⟨L.2, (proj_adj hP (dist_eq_three_of_adj_of_dist_eq_four hP hxy L.2)).symm⟩
    have hL'c : Γ.Adj x L'.1 ∧ Γ.Adj (f L).1 L'.1 := by
      refine ⟨L'.2, ?_⟩
      rw [hw]
      exact (proj_adj hP (dist_eq_three_of_adj_of_dist_eq_four hP hxy L'.2)).symm
    exact Subtype.ext ((existsUnique_commonNeighbor hP hxw).unique hLc hL'c)
  have hsurj : Function.Surjective f := by
    intro w
    have hxw : Γ.dist x w.1 = 2 := w.2.1
    let L : ↥(Γ.neighborSet x) :=
      ⟨commonNeighbor hP hxw, commonNeighbor_adj_left hP hxw⟩
    refine ⟨L, ?_⟩
    have hyL : Γ.dist y L.1 = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hxy L.2
    have hwproj : w.1 = proj hP hyL :=
      eq_proj hP hyL (commonNeighbor_adj_right hP hxw).symm w.2.2
    exact Subtype.ext hwproj.symm
  have hcard : Nat.card ↥(traceSet Γ x y) = Nat.card ↥(Γ.neighborSet x) :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
  calc
    (traceSet Γ x y).ncard = Nat.card ↥(traceSet Γ x y) := (Nat.card_coe_set_eq _).symm
    _ = Nat.card ↥(Γ.neighborSet x) := hcard
    _ = (Γ.neighborSet x).ncard := Nat.card_coe_set_eq _
    _ = Γ.degree x := by simp

theorem dist_eq_four_of_mem_trace (hP : IsGeneralizedPolygon Γ 4) {x y u v : V}
    (hxy : Γ.dist x y = 4) (hu : u ∈ traceSet Γ x y) (hv : v ∈ traceSet Γ x y)
    (huv : u ≠ v) : Γ.dist u v = 4 := by
  classical
  obtain ⟨c⟩ := hP.isBipartite
  have hxu : Γ.dist x u = 2 := hu.1
  have hxv : Γ.dist x v = 2 := hv.1
  have hcu : c u = c x := by
    rw [hP.eq_iff_even_dist c u x]
    rw [dist_comm, hxu]
    norm_num
  have hcv : c v = c x := by
    rw [hP.eq_iff_even_dist c v x]
    rw [dist_comm, hxv]
    norm_num
  have heven : Even (Γ.dist u v) := (hP.eq_iff_even_dist c u v).1 (hcu.trans hcv.symm)
  have hle : Γ.dist u v ≤ 4 := hP.dist_le (by norm_num) u v
  have hne0 : Γ.dist u v ≠ 0 := by
    intro h
    exact huv ((hP.connected.dist_eq_zero_iff).mp h)
  by_contra hne4
  have hd2 : Γ.dist u v = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  let L := commonNeighbor hP hxu
  have hLx : Γ.Adj x L := commonNeighbor_adj_left hP hxu
  have hLu : Γ.Adj u L := commonNeighbor_adj_right hP hxu
  obtain ⟨w, hw, -⟩ := existsUnique_commonNeighbor_of_pairwise_dist_two hP hxu hxv hd2
  have hwL : w = L :=
    (existsUnique_commonNeighbor hP hxu).unique ⟨hw.1, hw.2.1⟩ ⟨hLx, hLu⟩
  have hLv : Γ.Adj v L := by
    simpa [hwL] using hw.2.2
  have hyL : Γ.dist y L = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hxy hLx
  have hup : u = proj hP hyL := eq_proj hP hyL hLu.symm hu.2
  have hvp : v = proj hP hyL := eq_proj hP hyL hLv.symm hv.2
  exact huv (hup.trans hvp.symm)

theorem not_mem_spanSet_of_mem_traceSet [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {x y z : V} (hxy : Γ.dist x y = 4) (hz : z ∈ traceSet Γ x y) :
    z ∉ spanSet Γ x y := by
  intro hzs
  have htr2 : 1 < (traceSet Γ x y).ncard := by
    rw [ncard_trace hP hxy]
    exact lt_of_lt_of_le (by norm_num) (hT x)
  obtain ⟨w, hw, hwz⟩ := Set.exists_ne_of_one_lt_ncard htr2 z
  have h4 : Γ.dist z w = 4 := dist_eq_four_of_mem_trace hP hxy hz hw hwz.symm
  have h2 : Γ.dist z w ≤ 2 := hzs w hw
  omega

theorem spanSet_disjoint_traceSet [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {x y : V} (hxy : Γ.dist x y = 4) : Disjoint (spanSet Γ x y) (traceSet Γ x y) :=
  Set.disjoint_left.mpr fun z hz hz' => not_mem_spanSet_of_mem_traceSet hP hT hxy hz' hz

theorem left_mem_spanSet {x y : V} (hxy : Γ.dist x y = 4) : x ∈ spanSet Γ x y := by
  intro w hw
  exact le_of_eq hw.1

theorem right_mem_spanSet {x y : V} (hxy : Γ.dist x y = 4) : y ∈ spanSet Γ x y := by
  intro w hw
  exact le_of_eq hw.2

theorem color_eq_of_mem_span [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {x y z : V} (hxy : Γ.dist x y = 4) (hz : z ∈ spanSet Γ x y) : c z = c x := by
  by_contra hne
  have htr2 : 1 < (traceSet Γ x y).ncard := by
    rw [ncard_trace hP hxy]
    exact lt_of_lt_of_le (by norm_num) (hT x)
  obtain ⟨w1, hw1, w2, hw2, hne12⟩ := (Set.one_lt_ncard (s := traceSet Γ x y)).mp htr2
  have hdist1 : ∀ w, w ∈ traceSet Γ x y → Γ.dist z w = 1 := by
    intro w hw
    have hwc : c w = c x := by
      exact ((hP.eq_iff_even_dist c x w).2 (by rw [hw.1]; norm_num)).symm
    have hwz : c w ≠ c z := by
      intro h
      exact hne (by rw [← hwc, h])
    have hle : Γ.dist z w ≤ 2 := hz w hw
    have hpos : Γ.dist z w ≠ 0 := by
      intro h0
      have hzw : z = w := (hP.connected.dist_eq_zero_iff).mp h0
      exact hwz (by rw [hzw])
    have hodd : Odd (Γ.dist z w) := by
      by_contra h
      have heven : Even (Γ.dist z w) := Nat.not_odd_iff_even.mp h
      exact hwz ((hP.eq_iff_even_dist c z w).2 heven).symm
    obtain ⟨k, hk⟩ := hodd
    omega
  have h1 := hdist1 w1 hw1
  have h2 := hdist1 w2 hw2
  have h4 := dist_eq_four_of_mem_trace hP hxy hw1 hw2 hne12
  have hle12 : Γ.dist w1 w2 ≤ 2 := by
    have htri := hP.connected.dist_triangle (u := w1) (v := z) (w := w2)
    have d1 : Γ.dist w1 z = 1 := by rw [dist_comm]; exact h1
    omega
  omega

theorem dist_eq_two_of_mem_span_of_mem_trace [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) {x y z w : V}
    (hxy : Γ.dist x y = 4) (hz : z ∈ spanSet Γ x y) (hw : w ∈ traceSet Γ x y) :
    Γ.dist z w = 2 := by
  classical
  obtain ⟨c⟩ := hP.isBipartite
  have hcz : c z = c x := color_eq_of_mem_span hP hT c hxy hz
  have hwc : c w = c x :=
    ((hP.eq_iff_even_dist c x w).2 (by rw [hw.1]; norm_num)).symm
  have heven : Even (Γ.dist z w) := (hP.eq_iff_even_dist c z w).1 (hcz.trans hwc.symm)
  have hle : Γ.dist z w ≤ 2 := hz w hw
  have hne0 : Γ.dist z w ≠ 0 := by
    intro h0
    have hzw : z = w := (hP.connected.dist_eq_zero_iff).mp h0
    exact not_mem_spanSet_of_mem_traceSet hP hT hxy hw (hzw ▸ hz)
  obtain ⟨k, hk⟩ := heven
  omega

theorem dist_eq_four_of_mem_span [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) {x y z z' : V}
    (hxy : Γ.dist x y = 4) (hz : z ∈ spanSet Γ x y) (hz' : z' ∈ spanSet Γ x y)
    (hne : z ≠ z') : Γ.dist z z' = 4 := by
  classical
  obtain ⟨c⟩ := hP.isBipartite
  have hcz : c z = c x := color_eq_of_mem_span hP hT c hxy hz
  have hcz' : c z' = c x := color_eq_of_mem_span hP hT c hxy hz'
  have heven : Even (Γ.dist z z') := (hP.eq_iff_even_dist c z z').1 (hcz.trans hcz'.symm)
  have hle : Γ.dist z z' ≤ 4 := hP.dist_le (by norm_num) z z'
  have hne0 : Γ.dist z z' ≠ 0 := by
    intro h
    exact hne ((hP.connected.dist_eq_zero_iff).mp h)
  by_contra hne4
  have hd2 : Γ.dist z z' = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  let L := commonNeighbor hP hd2
  have hzL : Γ.Adj z L := commonNeighbor_adj_left hP hd2
  have hz'L : Γ.Adj z' L := commonNeighbor_adj_right hP hd2
  have hLnot : c L ≠ c x := by
    intro hLx
    exact (c.valid hzL) (hcz.trans hLx.symm)
  have htr2 : 1 < (traceSet Γ x y).ncard := by
    rw [ncard_trace hP hxy]
    exact lt_of_lt_of_le (by norm_num) (hT x)
  obtain ⟨w1, hw1, w2, hw2, hne12⟩ := (Set.one_lt_ncard (s := traceSet Γ x y)).mp htr2
  have hnotboth : ¬ (Γ.Adj w1 L ∧ Γ.Adj w2 L) := by
    rintro ⟨h1, h2⟩
    have hle12 : Γ.dist w1 w2 ≤ 2 := by
      have htri := hP.connected.dist_triangle (u := w1) (v := L) (w := w2)
      have d1 : Γ.dist w1 L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h1
      have d2 : Γ.dist L w2 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h2.symm
      omega
    have h4 := dist_eq_four_of_mem_trace hP hxy hw1 hw2 hne12
    omega
  obtain ⟨w, hw, hwL⟩ : ∃ w, w ∈ traceSet Γ x y ∧ ¬ Γ.Adj w L := by
    by_cases h1 : Γ.Adj w1 L
    · exact ⟨w2, hw2, fun h2 => hnotboth ⟨h1, h2⟩⟩
    · exact ⟨w1, hw1, h1⟩
  have hwc : c w = c x :=
    ((hP.eq_iff_even_dist c x w).2 (by rw [hw.1]; norm_num)).symm
  have hwLc : c w ≠ c L := by
    intro h
    exact hLnot (h.symm.trans hwc)
  have hwL3 : Γ.dist w L = 3 := by
    have hle3 : Γ.dist w L ≤ 3 := by
      have htri := hP.connected.dist_triangle (u := w) (v := z) (w := L)
      have d1 : Γ.dist w z = 2 := by
        rw [dist_comm]
        exact dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hz hw
      have d2 : Γ.dist z L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hzL
      omega
    have hnot1 : Γ.dist w L ≠ 1 := fun h =>
      hwL (SimpleGraph.dist_eq_one_iff_adj.mp h)
    have hnot2 : Γ.dist w L ≠ 2 := by
      intro h
      have heven : Even (Γ.dist w L) := by rw [h]; exact ⟨1, rfl⟩
      exact hwLc ((hP.eq_iff_even_dist c w L).2 heven)
    have hpos : 0 < Γ.dist w L := by
      by_contra h0
      have hzero : Γ.dist w L = 0 := by omega
      have hwLeq : w = L := (hP.connected.dist_eq_zero_iff).mp hzero
      exact hwLc (by rw [hwLeq])
    have hge1 : 1 ≤ Γ.dist w L := hpos
    have hcases : Γ.dist w L = 1 ∨ Γ.dist w L = 2 ∨ Γ.dist w L = 3 := by omega
    rcases hcases with h | h | h
    · exact absurd h hnot1
    · exact absurd h hnot2
    · exact h
  have hwz : Γ.dist z w = 2 :=
    dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hz hw
  have hwz' : Γ.dist z' w = 2 :=
    dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hz' hw
  exact hne ((existsUnique_proj hP hwL3).unique
    ⟨hzL.symm, by rw [dist_comm]; exact hwz⟩
    ⟨hz'L.symm, by rw [dist_comm]; exact hwz'⟩)

theorem span_eq_of_mem [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) {x y a b : V}
    (hxy : Γ.dist x y = 4) (ha : a ∈ spanSet Γ x y) (hb : b ∈ spanSet Γ x y)
    (hab : a ≠ b) :
    Γ.dist a b = 4 ∧ spanSet Γ a b = spanSet Γ x y ∧
      traceSet Γ a b = traceSet Γ x y := by
  classical
  have hab4 : Γ.dist a b = 4 := dist_eq_four_of_mem_span hP hT hxy ha hb hab
  have hsub : traceSet Γ x y ⊆ traceSet Γ a b := by
    intro w hw
    exact ⟨dist_eq_two_of_mem_span_of_mem_trace hP hT hxy ha hw,
      dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hb hw⟩
  have hdeg : Γ.degree a = Γ.degree x := by
    by_cases hax : a = x
    · rw [hax]
    · have hax4 : Γ.dist a x = 4 :=
        dist_eq_four_of_mem_span hP hT hxy ha (left_mem_spanSet hxy) hax
      exact hP.degree_eq_of_dist_eq (by norm_num) hax4
  have hcard : (traceSet Γ a b).ncard = (traceSet Γ x y).ncard := by
    calc
      (traceSet Γ a b).ncard = Γ.degree a := ncard_trace hP hab4
      _ = Γ.degree x := hdeg
      _ = (traceSet Γ x y).ncard := (ncard_trace hP hxy).symm
  have htrace : traceSet Γ x y = traceSet Γ a b :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard)
  refine ⟨hab4, ?_, htrace.symm⟩
  unfold spanSet
  rw [htrace]

theorem spanSet_subset_perpSet {x y u : V} (hu : u ∈ traceSet Γ x y) :
    spanSet Γ x y ⊆ perpSet Γ u := by
  intro z hz
  rw [mem_perpSet]
  rw [dist_comm]
  exact hz u hu

theorem ncard_spanSet_inter_neighborSet_le_one [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) {x y : V} (hxy : Γ.dist x y = 4)
    (L : V) : (spanSet Γ x y ∩ Γ.neighborSet L).ncard ≤ 1 := by
  rw [Set.ncard_le_one]
  intro z hz z' hz'
  by_contra hne
  have h4 : Γ.dist z z' = 4 := dist_eq_four_of_mem_span hP hT hxy hz.1 hz'.1 hne
  have hle : Γ.dist z z' ≤ 2 := by
    have htri := hP.connected.dist_triangle (u := z) (v := L) (w := z')
    have d1 : Γ.dist z L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hz.2.symm
    have d2 : Γ.dist L z' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hz'.2
    omega
  omega

end TraceAndSpan

section Colours

variable {Γ : SimpleGraph V}

theorem color_eq_one_of_adj_of_color_eq_zero {c : Γ.Coloring (Fin 2)} {x L : V}
    (hx : c x = 0) (h : Γ.Adj x L) : c L = 1 :=
  Fin.eq_one_of_ne_zero _ fun hL => c.valid h (hx.trans hL.symm)

theorem color_eq_zero_of_adj_of_color_eq_one {c : Γ.Coloring (Fin 2)} {L z : V}
    (hL : c L = 1) (h : Γ.Adj L z) : c z = 0 := by
  by_contra h0
  exact c.valid h (hL.trans (Fin.eq_one_of_ne_zero _ h0).symm)

end Colours

section Counting

variable {Γ : SimpleGraph V}
variable [Fintype V] [DecidableRel Γ.Adj]

@[expose] def pointFinset (c : Γ.Coloring (Fin 2)) : Finset V :=
  Finset.univ.filter fun v => c v = 0

@[expose] def lineFinset (c : Γ.Coloring (Fin 2)) : Finset V :=
  Finset.univ.filter fun v => c v = 1

@[simp] theorem mem_pointFinset {c : Γ.Coloring (Fin 2)} {v : V} :
    v ∈ pointFinset c ↔ c v = 0 := by
  simp [pointFinset]

@[simp] theorem mem_lineFinset {c : Γ.Coloring (Fin 2)} {v : V} :
    v ∈ lineFinset c ↔ c v = 1 := by
  simp [lineFinset]

theorem dist_eq_two_of_adj_of_adj_of_ne (hP : IsGeneralizedPolygon Γ 4) {x y L : V}
    (hxL : Γ.Adj x L) (hLy : Γ.Adj L y) (hxy : x ≠ y) : Γ.dist x y = 2 := by
  have h1 : Γ.dist x L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxL
  have htri := hP.connected.dist_triangle (u := x) (v := L) (w := y)
  rcases hP.dist_adj hLy x with h | h
  · omega
  · have hzero : Γ.dist x y = 0 := by omega
    exact absurd ((hP.connected.dist_eq_zero_iff).mp hzero) hxy

theorem card_collinear (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x : V}
    (hx : c x = 0) :
    (Finset.univ.filter fun y => Γ.dist x y = 2).card = s * (t + 1) := by
  classical
  let U := (Γ.neighborFinset x).biUnion fun L => (Γ.neighborFinset L).erase x
  have hset : (Finset.univ.filter fun y => Γ.dist x y = 2) = U := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, U, Finset.mem_biUnion,
      Finset.mem_erase, mem_neighborFinset]
    constructor
    · intro hy
      obtain ⟨L, ⟨hxL, hyL⟩, -⟩ := existsUnique_commonNeighbor hP hy
      exact ⟨L, hxL, by rintro rfl; simp at hy, hyL.symm⟩
    · rintro ⟨L, hxL, hyx, hLy⟩
      exact dist_eq_two_of_adj_of_adj_of_ne hP hxL hLy hyx.symm
  rw [hset, Finset.card_biUnion]
  · calc
      ∑ L ∈ Γ.neighborFinset x, ((Γ.neighborFinset L).erase x).card
          = ∑ L ∈ Γ.neighborFinset x, s := by
            refine Finset.sum_congr rfl fun L hL => ?_
            rw [Finset.card_erase_of_mem]
            · rw [card_neighborFinset_eq_degree, hdeg]
              have hcL : c L = 1 := by
                rw [mem_neighborFinset] at hL
                exact color_eq_one_of_adj_of_color_eq_zero hx hL
              rw [if_neg (by rw [hcL]; norm_num)]
              omega
            · rw [mem_neighborFinset]
              rw [mem_neighborFinset] at hL
              exact hL.symm
      _ = (Γ.neighborFinset x).card • s := Finset.sum_const s
      _ = s * (t + 1) := by
        rw [card_neighborFinset_eq_degree, hdeg, if_pos hx, smul_eq_mul]
        exact Nat.mul_comm (t + 1) s
  · intro L hL L' hL' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    simp only [Finset.mem_erase, mem_neighborFinset] at hy hy'
    have hLadj : Γ.Adj x L := by simpa using hL
    have hL'adj : Γ.Adj x L' := by simpa using hL'
    have hxy : Γ.dist x y = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hLadj hy.2 hy.1.symm
    exact hne ((existsUnique_commonNeighbor hP hxy).unique
      ⟨hLadj, hy.2.symm⟩ ⟨hL'adj, hy'.2.symm⟩)

theorem card_lines_off_point (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x : V}
    (hx : c x = 0) :
    (Finset.univ.filter fun L => Γ.dist x L = 3).card = s * t * (t + 1) := by
  classical
  let T : V → Finset V := fun y =>
    if hy : Γ.dist x y = 2 then (Γ.neighborFinset y).erase (commonNeighbor hP hy) else ∅
  let U := (Finset.univ.filter fun y => Γ.dist x y = 2).biUnion T
  have hset : (Finset.univ.filter fun L => Γ.dist x L = 3) = U := by
    ext L
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, T, U,
      Finset.mem_biUnion]
    constructor
    · intro hL
      let y := proj hP hL
      have hyL : Γ.Adj L y := proj_adj hP hL
      have hy : Γ.dist x y = 2 := proj_dist hP hL
      refine ⟨y, hy, ?_⟩
      have hmem : L ∈ (Γ.neighborFinset y).erase (commonNeighbor hP hy) := by
        rw [Finset.mem_erase, mem_neighborFinset]
        refine ⟨?_, hyL.symm⟩
        intro heq
        have hxcomm : Γ.dist x (commonNeighbor hP hy) = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr (commonNeighbor_adj_left hP hy)
        rw [heq] at hL
        omega
      simpa [T, hy] using hmem
    · rintro ⟨y, hy, hyT⟩
      have hmem : L ∈ (Γ.neighborFinset y).erase (commonNeighbor hP hy) := by
        simpa [T, hy] using hyT
      rw [Finset.mem_erase, mem_neighborFinset] at hmem
      have hLnotx : ¬ Γ.Adj x L := by
        intro hxL
        exact hmem.1 (eq_commonNeighbor hP hy hxL hmem.2)
      rcases hP.dist_adj hmem.2 x with h | h
      · omega
      · exfalso
        have h1 : Γ.dist x L = 1 := by omega
        exact hLnotx (SimpleGraph.dist_eq_one_iff_adj.mp h1)
  rw [hset, Finset.card_biUnion]
  · calc
      ∑ y ∈ Finset.univ.filter (fun y => Γ.dist x y = 2), (T y).card
          = ∑ y ∈ Finset.univ.filter (fun y => Γ.dist x y = 2), t := by
            refine Finset.sum_congr rfl fun y hy => ?_
            rw [Finset.mem_filter] at hy
            simp only [T, dif_pos hy.2]
            rw [Finset.card_erase_of_mem]
            · rw [card_neighborFinset_eq_degree, hdeg]
              have hcy : c y = 0 := by
                rw [← hx]
                exact ((hP.eq_iff_even_dist c x y).2 (by rw [hy.2]; norm_num)).symm
              rw [if_pos hcy]
              omega
            · simpa using commonNeighbor_adj_right hP hy.2
      _ = (Finset.univ.filter fun y => Γ.dist x y = 2).card • t := Finset.sum_const t
      _ = s * t * (t + 1) := by
        rw [card_collinear hP c hdeg hx, smul_eq_mul, Nat.mul_assoc, Nat.mul_assoc,
          Nat.mul_comm (t + 1) t]
  · intro y hy y' hy' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro L hL hL'
    have hy2 : Γ.dist x y = 2 := by simpa using hy
    have hy'2 : Γ.dist x y' = 2 := by simpa using hy'
    have hmem : L ∈ (Γ.neighborFinset y).erase (commonNeighbor hP hy2) := by
      simpa [T, hy2] using hL
    have hmem' : L ∈ (Γ.neighborFinset y').erase (commonNeighbor hP hy'2) := by
      simpa [T, hy'2] using hL'
    rw [Finset.mem_erase, mem_neighborFinset] at hmem hmem'
    have hLnotx : ¬ Γ.Adj x L := by
      intro hxL
      exact hmem.1 (eq_commonNeighbor hP hy2 hxL hmem.2)
    have hdist : Γ.dist x L = 3 := by
      rcases hP.dist_adj hmem.2 x with h | h
      · omega
      · exfalso
        have h1 : Γ.dist x L = 1 := by omega
        exact hLnotx (SimpleGraph.dist_eq_one_iff_adj.mp h1)
    exact hne ((existsUnique_proj hP hdist).unique
      ⟨hmem.2.symm, hy2⟩ ⟨hmem'.2.symm, hy'2⟩)

theorem exists_line (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) : ∃ v, c v = 1 := by
  classical
  obtain ⟨⟨v, hv⟩⟩ := hP.exists_point (by norm_num) hT c
  obtain ⟨L, hL⟩ : ∃ L, L ∈ Γ.neighborFinset v := by
    have h3 := hT v
    have hpos : 0 < (Γ.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree]
      omega
    exact Finset.card_pos.mp hpos
  rw [mem_neighborFinset] at hL
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hv hL
  exact ⟨L, hL1⟩

theorem two_le_s (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) : 2 ≤ s := by
  obtain ⟨L, hL⟩ := exists_line hP hT c
  have h3 := hT L
  rw [hdeg L, if_neg (by rw [hL]; decide)] at h3
  omega

theorem two_le_t (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) : 2 ≤ t := by
  obtain ⟨⟨x, hx⟩⟩ := hP.exists_point (by norm_num) hT c
  have h3 := hT x
  rw [hdeg x, if_pos hx] at h3
  omega

theorem dist_eq_three_of_not_adj_of_color_ne (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {x L : V} (hnot : ¬ Γ.Adj x L) (hc : c x ≠ c L) :
    Γ.dist x L = 3 := by
  have hodd : Odd (Γ.dist x L) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact hc ((hP.eq_iff_even_dist c x L).2 heven)
  have hle : Γ.dist x L ≤ 4 := hP.dist_le (by norm_num) x L
  have hne1 : Γ.dist x L ≠ 1 := fun h =>
    hnot (SimpleGraph.dist_eq_one_iff_adj.mp h)
  obtain ⟨k, hk⟩ := hodd
  omega

theorem card_lineFinset (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) :
    (lineFinset c).card = (t + 1) * (s * t + 1) := by
  classical
  obtain ⟨⟨x, hx⟩⟩ := hP.exists_point (by norm_num) hT c
  let Off := Finset.univ.filter fun L => Γ.dist x L = 3
  have hN : (Γ.neighborFinset x).card = t + 1 := by
    rw [card_neighborFinset_eq_degree, hdeg, if_pos hx]
  have hOff : Off.card = s * t * (t + 1) := card_lines_off_point hP c hdeg hx
  have hdisj : Disjoint (Γ.neighborFinset x) Off := by
    rw [Finset.disjoint_left]
    intro L hL hOff
    rw [mem_neighborFinset] at hL
    simp only [Off, Finset.mem_filter, Finset.mem_univ, true_and] at hOff
    have h1 : Γ.dist x L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hL
    omega
  have hunion : lineFinset c = Γ.neighborFinset x ∪ Off := by
    ext L
    constructor
    · intro hL
      rw [mem_lineFinset] at hL
      by_cases hxL : Γ.Adj x L
      · exact Finset.mem_union_left _ (by rwa [mem_neighborFinset])
      · refine Finset.mem_union_right _ ?_
        simp only [Off, Finset.mem_filter, Finset.mem_univ, true_and]
        exact dist_eq_three_of_not_adj_of_color_ne hP c hxL (by rw [hx, hL]; norm_num)
    · intro hL
      rcases Finset.mem_union.mp hL with hL | hL
      · rw [mem_neighborFinset] at hL
        have hne := c.valid hL
        have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
        rcases hfin (c L) with h | h
        · exact absurd (hx.trans h.symm) hne
        · exact mem_lineFinset.mpr h
      · simp only [Off, Finset.mem_filter, Finset.mem_univ, true_and] at hL
        have hne : c x ≠ c L := by
          intro hc
          have heven : Even (Γ.dist x L) := (hP.eq_iff_even_dist c x L).1 hc
          rw [hL] at heven
          exact (Nat.not_even_iff_odd.mpr ⟨1, by norm_num⟩) heven
        have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
        rcases hfin (c L) with h | h
        · exact absurd (hx.trans h.symm) hne
        · exact mem_lineFinset.mpr h
  rw [hunion, Finset.card_union_of_disjoint hdisj, hN, hOff]
  ring

theorem card_pointFinset (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) :
    (pointFinset c).card = (s + 1) * (s * t + 1) := by
  classical
  let dc : Γ.Coloring (Fin 2) := SimpleGraph.Coloring.mk (fun v => 1 - c v) (by
    intro v w h
    have hne := c.valid h
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c v) with hv | hv <;> rcases hfin (c w) with hw | hw
    · exact absurd (hv.trans hw.symm) hne
    · rw [hv, hw]; simp
    · rw [hv, hw]; simp
    · exact absurd (hv.trans hw.symm) hne)
  have hdeg' : ∀ v, Γ.degree v = if dc v = 0 then s + 1 else t + 1 := by
    intro v
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c v) with hv | hv
    · rw [hdeg, if_pos hv]
      have hdc : dc v ≠ 0 := by
        show 1 - c v ≠ 0
        rw [hv]
        decide
      rw [if_neg hdc]
    · rw [hdeg, if_neg (by rw [hv]; simp)]
      have hdc : dc v = 0 := by
        show 1 - c v = 0
        rw [hv]
        decide
      rw [if_pos hdc]
  have hdual : lineFinset dc = pointFinset c := by
    ext v
    rw [mem_lineFinset, mem_pointFinset]
    change (1 - c v = 1) ↔ c v = 0
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c v) with hv | hv
    · rw [hv]; simp
    · rw [hv]; simp
  have hline := card_lineFinset hP hT dc (s := t) (t := s) hdeg'
  rw [hdual] at hline
  simpa [Nat.mul_comm t s] using hline

theorem card_opposite (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x : V}
    (hx : c x = 0) :
    (Finset.univ.filter fun y => Γ.dist x y = 4).card = s ^ 2 * t := by
  classical
  let Coll := Finset.univ.filter fun y => Γ.dist x y = 2
  let Opp := Finset.univ.filter fun y => Γ.dist x y = 4
  have hpoint : pointFinset c = {x} ∪ Coll ∪ Opp := by
    ext y
    rw [mem_pointFinset]
    simp only [Finset.mem_union, Finset.mem_singleton, Coll, Opp, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hy
      have heven : Even (Γ.dist x y) := (hP.eq_iff_even_dist c x y).1 (hx.trans hy.symm)
      have hle : Γ.dist x y ≤ 4 := hP.dist_le (by norm_num) x y
      obtain ⟨k, hk⟩ := heven
      have hk2 : k ≤ 2 := by omega
      interval_cases k
      · refine Or.inl (Or.inl ?_)
        have h0 : Γ.dist x y = 0 := by simpa using hk
        exact ((hP.connected.dist_eq_zero_iff).mp h0).symm
      · refine Or.inl (Or.inr ?_)
        simpa using hk
      · refine Or.inr ?_
        simpa using hk
    · intro h
      rcases h with (hyx | h2) | h4
      · rw [hyx]; exact hx
      · rw [← hx]
        exact ((hP.eq_iff_even_dist c x y).2 ⟨1, by rw [h2]⟩).symm
      · rw [← hx]
        exact ((hP.eq_iff_even_dist c x y).2 ⟨2, by rw [h4]⟩).symm
  have hdisj1 : Disjoint ({x} : Finset V) Coll := by
    rw [Finset.disjoint_left]
    intro y hy hc
    simp only [Finset.mem_singleton] at hy
    subst hy
    simp only [Coll, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp at hc
  have hdisj2 : Disjoint Coll Opp := by
    rw [Finset.disjoint_left]
    intro y hy ho
    simp only [Coll, Opp, Finset.mem_filter, Finset.mem_univ, true_and] at hy ho
    omega
  have hdisj1' : Disjoint ({x} : Finset V) Opp := by
    rw [Finset.disjoint_left]
    intro y hy ho
    simp only [Finset.mem_singleton] at hy
    subst hy
    simp only [Opp, Finset.mem_filter, Finset.mem_univ, true_and] at ho
    simp at ho
  have hdisj_union : Disjoint ({x} ∪ Coll) Opp := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdisj1', hdisj2⟩
  have hcard : (pointFinset c).card = 1 + Coll.card + Opp.card := by
    rw [hpoint, Finset.card_union_of_disjoint hdisj_union,
      Finset.card_union_of_disjoint hdisj1, Finset.card_singleton]
  have hPcard : (pointFinset c).card = (s + 1) * (s * t + 1) :=
    card_pointFinset hP hT c hdeg
  have hCcard : Coll.card = s * (t + 1) := card_collinear hP c hdeg hx
  have hA : (s + 1) * (s * t + 1) = s ^ 2 * t + (1 + s * (t + 1)) := by ring
  have hsum : Opp.card + (1 + Coll.card) = (pointFinset c).card := by omega
  have hEq : Opp.card + (1 + Coll.card) = s ^ 2 * t + (1 + Coll.card) := by
    calc
      Opp.card + (1 + Coll.card) = (pointFinset c).card := hsum
      _ = (s + 1) * (s * t + 1) := hPcard
      _ = s ^ 2 * t + (1 + s * (t + 1)) := hA
      _ = s ^ 2 * t + (1 + Coll.card) := by rw [hCcard]
  exact Nat.add_right_cancel hEq

end Counting

end CFSG.Geometry.GeneralizedQuadrangles

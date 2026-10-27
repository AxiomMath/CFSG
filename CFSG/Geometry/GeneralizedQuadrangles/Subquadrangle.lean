module

public import CFSG.Geometry.GeneralizedQuadrangles.Basic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section Predicate

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

@[expose] def IsFullSubquadrangle (c : Γ.Coloring (Fin 2)) (P' : Set V) (t' : ℕ) : Prop :=
  (∀ x ∈ P', c x = 0) ∧
  (∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard → Γ.neighborSet L ⊆ P') ∧
  (∀ x ∈ P', {L | Γ.Adj x L ∧ Γ.neighborSet L ⊆ P'}.ncard = t' + 1) ∧
  (∃ x ∈ P', ∃ y ∈ P', Γ.dist x y = 4 ∧ 2 ≤ (traceSet Γ x y ∩ P').ncard)

@[expose] def subquadrangleLines (Γ : SimpleGraph V) (c : Γ.Coloring (Fin 2))
    (P' : Set V) : Set V :=
  {L | c L = 1 ∧ Γ.neighborSet L ⊆ P'}

@[expose] def subquadrangleSet (Γ : SimpleGraph V) (c : Γ.Coloring (Fin 2))
    (P' : Set V) : Set V :=
  P' ∪ subquadrangleLines Γ c P'

@[expose] def fullLinesThrough (Γ : SimpleGraph V) (P' : Set V) (x : V) : Set V :=
  {L | Γ.Adj x L ∧ Γ.neighborSet L ⊆ P'}

@[simp] theorem mem_subquadrangleLines {Γ : SimpleGraph V} {c : Γ.Coloring (Fin 2)}
    {P' : Set V} {L : V} :
    L ∈ subquadrangleLines Γ c P' ↔ c L = 1 ∧ Γ.neighborSet L ⊆ P' := Iff.rfl

@[simp] theorem mem_subquadrangleSet {Γ : SimpleGraph V} {c : Γ.Coloring (Fin 2)}
    {P' : Set V} {v : V} :
    v ∈ subquadrangleSet Γ c P' ↔ v ∈ P' ∨ c v = 1 ∧ Γ.neighborSet v ⊆ P' := by
  simp [subquadrangleSet, subquadrangleLines]

noncomputable instance instFintypeSubquadrangleSet {Γ : SimpleGraph V} [Fintype V]
    {c : Γ.Coloring (Fin 2)} (P' : Set V) : Fintype (subquadrangleSet Γ c P') :=
  (Set.toFinite _).fintype

@[simp] theorem mem_fullLinesThrough {Γ : SimpleGraph V} {P' : Set V} {x L : V} :
    L ∈ fullLinesThrough Γ P' x ↔ Γ.Adj x L ∧ Γ.neighborSet L ⊆ P' := Iff.rfl

end Predicate

section Basic

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem eq_of_two_common_points (hP : IsGeneralizedPolygon Γ 4) {L L' p q : V}
    (hpq : p ≠ q) (hLp : Γ.Adj L p) (hLq : Γ.Adj L q)
    (hL'p : Γ.Adj L' p) (hL'q : Γ.Adj L' q) : L = L' := by
  have h2 : Γ.dist p q = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hLp.symm hLq hpq
  exact (existsUnique_commonNeighbor hP h2).unique
    ⟨hLp.symm, hLq.symm⟩ ⟨hL'p.symm, hL'q.symm⟩

theorem ne_of_dist_eq_four_of_adj (hP : IsGeneralizedPolygon Γ 4) {x y L L' : V}
    (hxy : Γ.dist x y = 4) (hxL : Γ.Adj x L) (hyL' : Γ.Adj y L') : L ≠ L' := by
  intro h
  have hxL' : Γ.Adj x L' := h ▸ hxL
  have h1 : Γ.dist x L' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxL'
  have h2 : Γ.dist L' y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyL'.symm
  have h3 := hP.connected.dist_triangle (u := x) (v := L') (w := y)
  omega

structure QuadrangleFrame (Γ : SimpleGraph V) (P' : Set V) where
  x : V
  y : V
  u : V
  v : V
  A : V
  B : V
  C : V
  D : V
  hx : x ∈ P'
  hy : y ∈ P'
  hu : u ∈ P'
  hv : v ∈ P'
  hxy : Γ.dist x y = 4
  htu : u ∈ traceSet Γ x y
  htv : v ∈ traceSet Γ x y
  huv : u ≠ v
  hxA : Γ.Adj x A
  huA : Γ.Adj u A
  huB : Γ.Adj u B
  hyB : Γ.Adj y B
  hyC : Γ.Adj y C
  hvC : Γ.Adj v C
  hvD : Γ.Adj v D
  hxD : Γ.Adj x D

namespace QuadrangleFrame

variable {Γ : SimpleGraph V} {P' : Set V}

theorem hxu (F : QuadrangleFrame Γ P') : Γ.dist F.x F.u = 2 := by
  simpa using F.htu.1

theorem hyu (F : QuadrangleFrame Γ P') : Γ.dist F.y F.u = 2 := by
  simpa using F.htu.2

theorem hxv (F : QuadrangleFrame Γ P') : Γ.dist F.x F.v = 2 := by
  simpa using F.htv.1

theorem hyv (F : QuadrangleFrame Γ P') : Γ.dist F.y F.v = 2 := by
  simpa using F.htv.2

theorem huv_dist (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P') :
    Γ.dist F.u F.v = 4 :=
  dist_eq_four_of_mem_trace hP F.hxy F.htu F.htv F.huv

theorem hxu_ne (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P') : F.x ≠ F.u := by
  intro h
  have h2 : Γ.dist F.x F.u = 2 := F.hxu
  rw [h] at h2
  simp at h2

theorem hxv_ne (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P') : F.x ≠ F.v := by
  intro h
  have h2 : Γ.dist F.x F.v = 2 := F.hxv
  rw [h] at h2
  simp at h2

theorem hyu_ne (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P') : F.y ≠ F.u := by
  intro h
  have h2 : Γ.dist F.y F.u = 2 := F.hyu
  rw [h] at h2
  simp at h2

theorem hyv_ne (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P') : F.y ≠ F.v := by
  intro h
  have h2 : Γ.dist F.y F.v = 2 := F.hyv
  rw [h] at h2
  simp at h2

end QuadrangleFrame

theorem exists_quadrangleFrame (hP : IsGeneralizedPolygon Γ 4) {P' : Set V}
    (hquad : ∃ x ∈ P', ∃ y ∈ P', Γ.dist x y = 4 ∧
      2 ≤ (traceSet Γ x y ∩ P').ncard) :
    Nonempty (QuadrangleFrame Γ P') := by
  classical
  obtain ⟨x, hx, y, hy, hxy, htr⟩ := hquad
  have htr' : 1 < (traceSet Γ x y ∩ P').ncard := by omega
  obtain ⟨u, hu, v, hv, huv⟩ :=
    (Set.one_lt_ncard (s := traceSet Γ x y ∩ P')).mp htr'
  have htu : u ∈ traceSet Γ x y := hu.1
  have huP : u ∈ P' := hu.2
  have htv : v ∈ traceSet Γ x y := hv.1
  have hvP : v ∈ P' := hv.2
  have hxu : Γ.dist x u = 2 := by simpa using htu.1
  have huy : Γ.dist u y = 2 := by
    rw [dist_comm]
    simpa using htu.2
  have hyv : Γ.dist y v = 2 := by simpa using htv.2
  have hxv : Γ.dist x v = 2 := by simpa using htv.1
  let A := commonNeighbor hP hxu
  let B := commonNeighbor hP huy
  let C := commonNeighbor hP hyv
  let D := commonNeighbor hP hxv
  exact ⟨{
    x := x, y := y, u := u, v := v, A := A, B := B, C := C, D := D,
    hx := hx, hy := hy, hu := huP, hv := hvP,
    hxy := hxy, htu := htu, htv := htv, huv := huv,
    hxA := commonNeighbor_adj_left hP hxu,
    huA := commonNeighbor_adj_right hP hxu,
    huB := commonNeighbor_adj_left hP huy,
    hyB := commonNeighbor_adj_right hP huy,
    hyC := commonNeighbor_adj_left hP hyv,
    hvC := commonNeighbor_adj_right hP hyv,
    hvD := commonNeighbor_adj_right hP hxv,
    hxD := commonNeighbor_adj_left hP hxv }⟩

namespace QuadrangleFrame

variable {c : Γ.Coloring (Fin 2)} {P' : Set V}

theorem color_A (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P')
    (h0 : ∀ x ∈ P', c x = 0) : c F.A = 1 :=
  color_eq_one_of_adj_of_color_eq_zero (h0 F.x F.hx) F.hxA

theorem color_B (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P')
    (h0 : ∀ x ∈ P', c x = 0) : c F.B = 1 :=
  color_eq_one_of_adj_of_color_eq_zero (h0 F.y F.hy) F.hyB

theorem color_C (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P')
    (h0 : ∀ x ∈ P', c x = 0) : c F.C = 1 :=
  color_eq_one_of_adj_of_color_eq_zero (h0 F.y F.hy) F.hyC

theorem color_D (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P')
    (h0 : ∀ x ∈ P', c x = 0) : c F.D = 1 :=
  color_eq_one_of_adj_of_color_eq_zero (h0 F.x F.hx) F.hxD

theorem full_A (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P')
    (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P') : Γ.neighborSet F.A ⊆ P' := by
  have hne : F.x ≠ F.u := F.hxu_ne hP
  have h2 : 2 ≤ (Γ.neighborSet F.A ∩ P').ncard := by
    have h2' : 1 < (Γ.neighborSet F.A ∩ P').ncard :=
      (Set.one_lt_ncard (s := Γ.neighborSet F.A ∩ P')).mpr
        ⟨F.x, ⟨F.hxA.symm, F.hx⟩, F.u, ⟨F.huA.symm, F.hu⟩, hne⟩
    omega
  exact hfull F.A (F.color_A hP h0) h2

theorem full_B (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P')
    (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P') : Γ.neighborSet F.B ⊆ P' := by
  have hne : F.u ≠ F.y := (F.hyu_ne hP).symm
  have h2 : 2 ≤ (Γ.neighborSet F.B ∩ P').ncard := by
    have h2' : 1 < (Γ.neighborSet F.B ∩ P').ncard :=
      (Set.one_lt_ncard (s := Γ.neighborSet F.B ∩ P')).mpr
        ⟨F.u, ⟨F.huB.symm, F.hu⟩, F.y, ⟨F.hyB.symm, F.hy⟩, hne⟩
    omega
  exact hfull F.B (F.color_B hP h0) h2

theorem full_C (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P')
    (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P') : Γ.neighborSet F.C ⊆ P' := by
  have hne : F.y ≠ F.v := F.hyv_ne hP
  have h2 : 2 ≤ (Γ.neighborSet F.C ∩ P').ncard := by
    have h2' : 1 < (Γ.neighborSet F.C ∩ P').ncard :=
      (Set.one_lt_ncard (s := Γ.neighborSet F.C ∩ P')).mpr
        ⟨F.y, ⟨F.hyC.symm, F.hy⟩, F.v, ⟨F.hvC.symm, F.hv⟩, hne⟩
    omega
  exact hfull F.C (F.color_C hP h0) h2

theorem full_D (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P')
    (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P') : Γ.neighborSet F.D ⊆ P' := by
  have hne : F.v ≠ F.x := (F.hxv_ne hP).symm
  have h2 : 2 ≤ (Γ.neighborSet F.D ∩ P').ncard := by
    have h2' : 1 < (Γ.neighborSet F.D ∩ P').ncard :=
      (Set.one_lt_ncard (s := Γ.neighborSet F.D ∩ P')).mpr
        ⟨F.v, ⟨F.hvD.symm, F.hv⟩, F.x, ⟨F.hxD.symm, F.hx⟩, hne⟩
    omega
  exact hfull F.D (F.color_D hP h0) h2

theorem A_ne_B (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P') :
    F.A ≠ F.B :=
  ne_of_dist_eq_four_of_adj hP F.hxy F.hxA F.hyB

theorem A_ne_D (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P') :
    F.A ≠ F.D :=
  ne_of_dist_eq_four_of_adj hP (F.huv_dist hP) F.huA F.hvD

end QuadrangleFrame

theorem disjoint_neighborSet_of_mem_trace (hP : IsGeneralizedPolygon Γ 4)
    {x y u v A C : V} (hxy : Γ.dist x y = 4)
    (hu : u ∈ traceSet Γ x y) (hv : v ∈ traceSet Γ x y) (huv : u ≠ v)
    (hAx : Γ.Adj A x) (hAu : Γ.Adj A u)
    (hCy : Γ.Adj C y) (hCv : Γ.Adj C v) :
    Disjoint (Γ.neighborSet A) (Γ.neighborSet C) := by
  rw [Set.disjoint_left]
  intro p hpA hpC
  have hpAx : Γ.Adj A p := hpA
  have hpCx : Γ.Adj C p := hpC
  have hxp : Γ.dist x p = 2 := by
    have hpx : p ≠ x := by
      intro hpx
      have hxC : Γ.Adj C x := by rw [← hpx]; exact hpCx
      have hxy2 : Γ.dist x y = 2 := by
        have hne : x ≠ y := by
          intro h
          rw [h] at hxy
          simp at hxy
        exact dist_eq_two_of_adj_of_adj_of_ne hP hxC.symm hCy hne
      omega
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_adj_of_adj_of_ne hP hpAx.symm hAx hpx
  have hyp : Γ.dist y p = 2 := by
    have hpy : p ≠ y := by
      intro hpy
      have hyA : Γ.Adj A y := by rw [← hpy]; exact hpAx
      have hyx2 : Γ.dist y x = 2 := by
        have hne : y ≠ x := by
          intro h
          rw [h] at hxy
          simp at hxy
        exact dist_eq_two_of_adj_of_adj_of_ne hP hyA.symm hAx hne
      rw [SimpleGraph.dist_comm] at hyx2
      omega
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_adj_of_adj_of_ne hP hpCx.symm hCy hpy
  have hpt : p ∈ traceSet Γ x y := ⟨hxp, hyp⟩
  by_cases hpu : p = u
  · subst hpu
    have h2 : Γ.dist p v = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hpCx.symm hCv huv
    have h4 : Γ.dist p v = 4 :=
      dist_eq_four_of_mem_trace hP hxy hpt hv huv
    omega
  · have h2 : Γ.dist p u = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hpAx.symm hAu hpu
    have h4 : Γ.dist p u = 4 :=
      dist_eq_four_of_mem_trace hP hxy hpt hu hpu
    omega

namespace QuadrangleFrame

variable {c : Γ.Coloring (Fin 2)} {P' : Set V}

theorem disjoint_AC (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P') :
    Disjoint (Γ.neighborSet F.A) (Γ.neighborSet F.C) :=
  disjoint_neighborSet_of_mem_trace hP F.hxy F.htu F.htv F.huv
    F.hxA.symm F.huA.symm F.hyC.symm F.hvC.symm

theorem disjoint_BD (hP : IsGeneralizedPolygon Γ 4) (F : QuadrangleFrame Γ P') :
    Disjoint (Γ.neighborSet F.B) (Γ.neighborSet F.D) := by
  have htu' : F.u ∈ traceSet Γ F.y F.x :=
    ⟨by simpa using F.htu.2, by simpa using F.htu.1⟩
  have htv' : F.v ∈ traceSet Γ F.y F.x :=
    ⟨by simpa using F.htv.2, by simpa using F.htv.1⟩
  have hxy' : Γ.dist F.y F.x = 4 := by rw [SimpleGraph.dist_comm]; exact F.hxy
  exact disjoint_neighborSet_of_mem_trace hP hxy' htu' htv' F.huv
    F.hyB.symm F.huB.symm F.hxD.symm F.hvD.symm

end QuadrangleFrame

theorem exists_fullLineThrough (hP : IsGeneralizedPolygon Γ 4) {c : Γ.Coloring (Fin 2)}
    {P' : Set V} (F : QuadrangleFrame Γ P') (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P') {a : V} (ha : a ∈ P') :
    ∃ L, Γ.Adj a L ∧ Γ.neighborSet L ⊆ P' := by
  classical
  by_cases haA : Γ.Adj a F.A
  · exact ⟨F.A, haA, F.full_A hP h0 hfull⟩
  · have hca : c a = 0 := h0 a ha
    have hcA : c F.A = 1 := F.color_A hP h0
    have hcne : c a ≠ c F.A := by rw [hca, hcA]; decide
    have h3 : Γ.dist a F.A = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c haA hcne
    let w := proj hP h3
    have hAw : Γ.Adj F.A w := proj_adj hP h3
    have haw : Γ.dist a w = 2 := proj_dist hP h3
    have hwP : w ∈ P' := F.full_A hP h0 hfull hAw
    let L := commonNeighbor hP haw
    have haL : Γ.Adj a L := commonNeighbor_adj_left hP haw
    have hLfull : Γ.neighborSet L ⊆ P' := by
      have hne : a ≠ w := by
        intro h
        rw [h] at haw
        simp at haw
      have h2' : 1 < (Γ.neighborSet L ∩ P').ncard :=
        (Set.one_lt_ncard (s := Γ.neighborSet L ∩ P')).mpr
          ⟨a, ⟨haL.symm, ha⟩, w,
            ⟨(commonNeighbor_adj_right hP haw).symm, hwP⟩, hne⟩
      exact hfull L (color_eq_one_of_adj_of_color_eq_zero hca haL) (by omega)
    exact ⟨L, haL, hLfull⟩

theorem eq_left_or_eq_right_of_three_lines (hP : IsGeneralizedPolygon Γ 4)
    {M A B pA pB u : V} (hAB : A ≠ B) (hMA : M ≠ A)
    (hMpA : Γ.Adj M pA) (hMpB : Γ.Adj M pB)
    (hApA : Γ.Adj A pA) (hAu : Γ.Adj A u)
    (hBpB : Γ.Adj B pB) (hBu : Γ.Adj B u) :
    pA = u ∨ pB = u := by
  by_cases hpApB : pA = pB
  · left
    by_contra hpAu
    have hBpA : Γ.Adj B pA := by rw [hpApB]; exact hBpB
    exact hAB (eq_of_two_common_points hP (Ne.symm hpAu) hAu hApA hBu hBpA)
  · by_contra h
    push Not at h
    obtain ⟨hpAu, hpBu⟩ := h
    have h2p : Γ.dist pA pB = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hMpA.symm hMpB hpApB
    have h2u : Γ.dist pA u = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hApA.symm hAu hpAu
    have h2b : Γ.dist pB u = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hBpB.symm hBu hpBu
    obtain ⟨W, hW, -⟩ :=
      existsUnique_commonNeighbor_of_pairwise_dist_two hP h2p h2u h2b
    have hWM : W = M :=
      (existsUnique_commonNeighbor hP h2p).unique ⟨hW.1, hW.2.1⟩
        ⟨hMpA.symm, hMpB.symm⟩
    have hWA : W = A :=
      (existsUnique_commonNeighbor hP h2u).unique ⟨hW.1, hW.2.2⟩
        ⟨hApA.symm, hAu.symm⟩
    exact hMA (hWM.symm.trans hWA)

theorem two_le_ncard_fullLinesThrough (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {P' : Set V} (F : QuadrangleFrame Γ P')
    (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P') {a : V} (ha : a ∈ P') :
    2 ≤ (fullLinesThrough Γ P' a).ncard := by
  classical
  obtain ⟨L0, haL0, hL0full⟩ := exists_fullLineThrough hP F h0 hfull ha
  have hL0mem : L0 ∈ fullLinesThrough Γ P' a := ⟨haL0, hL0full⟩
  by_contra hlt
  have hle : (fullLinesThrough Γ P' a).ncard ≤ 1 := by omega
  have huniq : ∀ L ∈ fullLinesThrough Γ P' a,
      ∀ M ∈ fullLinesThrough Γ P' a, L = M :=
    (Set.ncard_le_one (Set.toFinite _)).mp hle
  have hca : c a = 0 := h0 a ha
  have proj_mem : ∀ {B : V}, B ∈ subquadrangleLines Γ c P' → ¬ Γ.Adj a B →
      ∃ w, w ∈ P' ∧ Γ.Adj B w ∧ Γ.dist a w = 2 ∧ Γ.Adj L0 w := by
    intro B hB hnotB
    have hcB : c B = 1 := (mem_subquadrangleLines.mp hB).1
    have hBfull : Γ.neighborSet B ⊆ P' := (mem_subquadrangleLines.mp hB).2
    have hcne : c a ≠ c B := by rw [hca, hcB]; decide
    have h3 : Γ.dist a B = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c hnotB hcne
    let w := proj hP h3
    have hBw : Γ.Adj B w := proj_adj hP h3
    have haw : Γ.dist a w = 2 := proj_dist hP h3
    have hwP : w ∈ P' := hBfull hBw
    let L := commonNeighbor hP haw
    have haL : Γ.Adj a L := commonNeighbor_adj_left hP haw
    have hLw : Γ.Adj L w := (commonNeighbor_adj_right hP haw).symm
    have hLfull : Γ.neighborSet L ⊆ P' := by
      have hne : a ≠ w := by
        intro h
        rw [h] at haw
        simp at haw
      have h2' : 1 < (Γ.neighborSet L ∩ P').ncard :=
        (Set.one_lt_ncard (s := Γ.neighborSet L ∩ P')).mpr
          ⟨a, ⟨haL.symm, ha⟩, w, ⟨hLw, hwP⟩, hne⟩
      exact hfull L (color_eq_one_of_adj_of_color_eq_zero hca haL) (by omega)
    have hLmem : L ∈ fullLinesThrough Γ P' a := ⟨haL, hLfull⟩
    have hLeq : L = L0 := huniq L hLmem L0 hL0mem
    exact ⟨w, hwP, hBw, haw, hLeq ▸ hLw⟩
  have hnotA : ¬ Γ.Adj a F.A := by
    intro haA
    have hAmem : F.A ∈ fullLinesThrough Γ P' a :=
      ⟨haA, F.full_A hP h0 hfull⟩
    have haC : ¬ Γ.Adj a F.C := by
      intro haC
      exact (Set.disjoint_left.mp (F.disjoint_AC hP)) haA.symm haC.symm
    obtain ⟨w, -, hCw, -, hL0w⟩ :=
      proj_mem (B := F.C) ⟨F.color_C hP h0, F.full_C hP h0 hfull⟩ haC
    have hAeq : F.A = L0 := huniq F.A hAmem L0 hL0mem
    exact (Set.disjoint_left.mp (F.disjoint_AC hP)) (hAeq.symm ▸ hL0w) hCw
  have hnotB : ¬ Γ.Adj a F.B := by
    intro haB
    have hBmem : F.B ∈ fullLinesThrough Γ P' a :=
      ⟨haB, F.full_B hP h0 hfull⟩
    have haD : ¬ Γ.Adj a F.D := by
      intro haD
      exact (Set.disjoint_left.mp (F.disjoint_BD hP)) haB.symm haD.symm
    obtain ⟨w, -, hDw, -, hL0w⟩ :=
      proj_mem (B := F.D) ⟨F.color_D hP h0, F.full_D hP h0 hfull⟩ haD
    have hBeq : F.B = L0 := huniq F.B hBmem L0 hL0mem
    exact (Set.disjoint_left.mp (F.disjoint_BD hP)) (hBeq.symm ▸ hL0w) hDw
  have hnotD : ¬ Γ.Adj a F.D := by
    intro haD
    have hDmem : F.D ∈ fullLinesThrough Γ P' a :=
      ⟨haD, F.full_D hP h0 hfull⟩
    have haB : ¬ Γ.Adj a F.B := by
      intro haB
      exact (Set.disjoint_left.mp (F.disjoint_BD hP)) haB.symm haD.symm
    obtain ⟨w, -, hBw, -, hL0w⟩ :=
      proj_mem (B := F.B) ⟨F.color_B hP h0, F.full_B hP h0 hfull⟩ haB
    have hDeq : F.D = L0 := huniq F.D hDmem L0 hL0mem
    exact (Set.disjoint_left.mp (F.disjoint_BD hP)) hBw (hDeq.symm ▸ hL0w)
  obtain ⟨pA, -, hApA, -, hpAL0⟩ :=
    proj_mem (B := F.A) ⟨F.color_A hP h0, F.full_A hP h0 hfull⟩ hnotA
  obtain ⟨pB, -, hBpB, -, hpBL0⟩ :=
    proj_mem (B := F.B) ⟨F.color_B hP h0, F.full_B hP h0 hfull⟩ hnotB
  obtain ⟨pD, -, hDpD, -, hpDL0⟩ :=
    proj_mem (B := F.D) ⟨F.color_D hP h0, F.full_D hP h0 hfull⟩ hnotD
  have hMA : L0 ≠ F.A := fun h => hnotA (by rw [← h]; exact haL0)
  have h1 : pA = F.u ∨ pB = F.u :=
    eq_left_or_eq_right_of_three_lines hP (F.A_ne_B hP) hMA hpAL0 hpBL0
      hApA F.huA.symm hBpB F.huB.symm
  have h2 : pA = F.x ∨ pD = F.x :=
    eq_left_or_eq_right_of_three_lines hP (F.A_ne_D hP) hMA hpAL0 hpDL0
      hApA F.hxA.symm hDpD F.hxD.symm
  rcases h1 with hpu | hpu <;> rcases h2 with hpx | hpx
  · exact F.hxu_ne hP (hpu.symm.trans hpx).symm
  · have hM : L0 = F.A :=
      eq_of_two_common_points hP (F.hxu_ne hP).symm
        (hpu ▸ hpAL0) (hpx ▸ hpDL0) F.huA.symm F.hxA.symm
    exact hMA hM
  · have hM : L0 = F.A :=
      eq_of_two_common_points hP (F.hxu_ne hP).symm
        (hpu ▸ hpBL0) (hpx ▸ hpAL0) F.huA.symm F.hxA.symm
    exact hMA hM
  · have hM : L0 = F.A :=
      eq_of_two_common_points hP (F.hxu_ne hP).symm
        (hpu ▸ hpBL0) (hpx ▸ hpDL0) F.huA.symm F.hxA.symm
    exact hMA hM

theorem ncard_of_isFullSubquadrangle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {t' : ℕ} {P' : Set V} (hF : IsFullSubquadrangle c P' t') :
    P'.ncard = (s + 1) * (s * t' + 1) := by
  classical
  have h0 : ∀ x ∈ P', c x = 0 := hF.1
  have hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P' := hF.2.1
  have hn : ∀ x ∈ P', {L | Γ.Adj x L ∧ Γ.neighborSet L ⊆ P'}.ncard = t' + 1 := hF.2.2.1
  obtain ⟨F⟩ := exists_quadrangleFrame hP hF.2.2.2
  obtain ⟨L0, hL0adj, hL0full⟩ := exists_fullLineThrough hP F h0 hfull F.hx
  have hcL0 : c L0 = 1 := color_eq_one_of_adj_of_color_eq_zero (h0 F.x F.hx) hL0adj
  let Pfin : Finset V := P'.toFinset
  let lineFinset : V → Finset V := fun p =>
    Finset.univ.filter fun M => Γ.Adj p M ∧ Γ.neighborSet M ⊆ P'
  let C : V → Finset V := fun p =>
    ((lineFinset p).erase L0).biUnion fun M => (Γ.neighborFinset M).erase p
  have hNcard : (Γ.neighborFinset L0).card = s + 1 := by
    rw [card_neighborFinset_eq_degree, hdeg L0, if_neg (by rw [hcL0]; decide)]
  have hlineFinset_card : ∀ p ∈ Γ.neighborFinset L0, (lineFinset p).card = t' + 1 := by
    intro p hp
    have hpP : p ∈ P' := hL0full (by simpa using hp)
    have hset : lineFinset p =
        {L | Γ.Adj p L ∧ Γ.neighborSet L ⊆ P'}.toFinset := by
      ext L
      simp [lineFinset]
    rw [hset, ← Set.ncard_eq_toFinset_card']
    exact hn p hpP
  have hCcard : ∀ p ∈ Γ.neighborFinset L0, (C p).card = t' * s := by
    intro p hp
    have hpP : p ∈ P' := hL0full (by simpa using hp)
    have hpL0 : L0 ∈ lineFinset p := by
      have hL0p : Γ.Adj L0 p := by simpa using hp
      simp only [lineFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hL0p.symm, hL0full⟩
    have hmem : ∀ M ∈ (lineFinset p).erase L0,
        ((Γ.neighborFinset M).erase p).card = s := by
      intro M hM
      rw [Finset.mem_erase] at hM
      obtain ⟨-, hMline⟩ := hM
      simp only [lineFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hMline
      obtain ⟨hpM, -⟩ := hMline
      have hcM : c M = 1 := color_eq_one_of_adj_of_color_eq_zero (h0 p hpP) hpM
      have hMdeg : Γ.degree M = s + 1 := by
        rw [hdeg M, if_neg (by rw [hcM]; decide)]
      rw [Finset.card_erase_of_mem (by simpa using hpM.symm), card_neighborFinset_eq_degree,
        hMdeg]
      omega
    have hdisj : (↑((lineFinset p).erase L0) : Set V).PairwiseDisjoint
        (fun M => (Γ.neighborFinset M).erase p) := by
      intro M hM M' hM' hne
      have hM' := hM'
      rw [Finset.mem_coe, Finset.mem_erase] at hM hM'
      obtain ⟨-, hMline⟩ := hM
      obtain ⟨-, hM'line⟩ := hM'
      simp only [lineFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hMline hM'line
      obtain ⟨hpM, -⟩ := hMline
      obtain ⟨hpM', -⟩ := hM'line
      rw [Function.onFun, Finset.disjoint_left]
      intro z hz hz'
      rw [Finset.mem_erase, mem_neighborFinset] at hz hz'
      exact hne (eq_of_two_common_points hP (Ne.symm hz.1) hpM.symm hz.2 hpM'.symm hz'.2)
    change (((lineFinset p).erase L0).biUnion
      fun M => (Γ.neighborFinset M).erase p).card = t' * s
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl hmem, Finset.sum_const, smul_eq_mul]
      have herase : ((lineFinset p).erase L0).card = t' := by
        rw [Finset.card_erase_of_mem hpL0, hlineFinset_card p hp]
        omega
      rw [herase]
    · exact hdisj
  have hdisjN : Disjoint (Γ.neighborFinset L0)
      ((Γ.neighborFinset L0).biUnion C) := by
    rw [Finset.disjoint_left]
    intro z hzN hzC
    rw [Finset.mem_biUnion] at hzC
    obtain ⟨p, hp, hzp⟩ := hzC
    dsimp only [C] at hzp
    rw [Finset.mem_biUnion] at hzp
    obtain ⟨M, hM, hzM⟩ := hzp
    rw [Finset.mem_erase] at hM hzM
    obtain ⟨hML0, hMline⟩ := hM
    obtain ⟨hzpne, hzMmem⟩ := hzM
    simp only [lineFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hMline
    obtain ⟨hpM, -⟩ := hMline
    exact hML0 ((eq_of_two_common_points hP (Ne.symm hzpne) (by simpa using hp)
      (by simpa using hzN) hpM.symm (by simpa using hzMmem)).symm)
  have hdisjC : (↑(Γ.neighborFinset L0) : Set V).PairwiseDisjoint C := by
    intro p hp p' hp' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz hz'
    dsimp only [C] at hz hz'
    rw [Finset.mem_biUnion] at hz hz'
    obtain ⟨M, hM, hzM⟩ := hz
    obtain ⟨M', hM', hzM'⟩ := hz'
    rw [Finset.mem_erase] at hM hM' hzM hzM'
    obtain ⟨hML0, hMline⟩ := hM
    obtain ⟨hM'L0, hM'line⟩ := hM'
    obtain ⟨hzpne, hzMmem⟩ := hzM
    obtain ⟨hzp'ne, hzM'mem⟩ := hzM'
    simp only [lineFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hMline hM'line
    obtain ⟨hpM, hMfull⟩ := hMline
    obtain ⟨hp'M, hM'full⟩ := hM'line
    have hzP : z ∈ P' := hMfull (by simpa using hzMmem)
    have hzL0 : ¬ Γ.Adj L0 z := by
      intro hzL0
      exact hML0 ((eq_of_two_common_points hP (Ne.symm hzpne) (by simpa using hp)
        hzL0 hpM.symm (by simpa using hzMmem)).symm)
    have hcz : c z = 0 := h0 z hzP
    have hzL3 : Γ.dist z L0 = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hzL0 h.symm)
        (by rw [hcz, hcL0]; decide)
    have hzp2 : Γ.dist z p = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP
        (by simpa using hzMmem : Γ.Adj M z).symm hpM.symm hzpne
    have hzp'2 : Γ.dist z p' = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP
        (by simpa using hzM'mem : Γ.Adj M' z).symm hp'M.symm hzp'ne
    have h1 : p = proj hP hzL3 := eq_proj hP hzL3 (by simpa using hp) hzp2
    have h2 : p' = proj hP hzL3 := eq_proj hP hzL3 (by simpa using hp') hzp'2
    exact hne (h1.trans h2.symm)
  have hPfin_eq : Pfin = Γ.neighborFinset L0 ∪ (Γ.neighborFinset L0).biUnion C := by
    ext z
    constructor
    · intro hz
      have hzP : z ∈ P' := by simpa [Pfin] using hz
      by_cases hzL0 : Γ.Adj L0 z
      · exact Finset.mem_union_left _ (by simpa using hzL0)
      · rw [Finset.mem_union]
        right
        have hcz : c z = 0 := h0 z hzP
        have hz3 : Γ.dist z L0 = 3 :=
          dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hzL0 h.symm)
            (by rw [hcz, hcL0]; decide)
        let p := proj hP hz3
        have hpN : Γ.Adj L0 p := proj_adj hP hz3
        have hpP : p ∈ P' := hL0full (by simpa using hpN)
        have hzp : Γ.dist z p = 2 := proj_dist hP hz3
        let M := commonNeighbor hP hzp
        have hzM : Γ.Adj z M := commonNeighbor_adj_left hP hzp
        have hpM : Γ.Adj p M := commonNeighbor_adj_right hP hzp
        have hne : z ≠ p := by
          intro h
          rw [h] at hzp
          simp at hzp
        have hMfull : Γ.neighborSet M ⊆ P' := by
          have h2' : 1 < (Γ.neighborSet M ∩ P').ncard :=
            (Set.one_lt_ncard (s := Γ.neighborSet M ∩ P')).mpr
              ⟨z, ⟨hzM.symm, hzP⟩, p, ⟨hpM.symm, hpP⟩, hne⟩
          exact hfull M (color_eq_one_of_adj_of_color_eq_zero hcz hzM) (by omega)
        have hML0 : M ≠ L0 := by
          intro h
          exact hzL0 (by rw [h] at hzM; exact hzM.symm)
        refine Finset.mem_biUnion.mpr ⟨p, by simpa using hpN, ?_⟩
        refine Finset.mem_biUnion.mpr ⟨M, ?_, ?_⟩
        · rw [Finset.mem_erase]
          exact ⟨hML0, by simp [lineFinset, hpM, hMfull]⟩
        · rw [Finset.mem_erase]
          exact ⟨hne, by simpa using hzM.symm⟩
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact by simpa [Pfin] using hL0full (by simpa using hz)
      · rw [Finset.mem_biUnion] at hz
        obtain ⟨p, -, hzC⟩ := hz
        dsimp only [C] at hzC
        rw [Finset.mem_biUnion] at hzC
        obtain ⟨M, hM, hzM⟩ := hzC
        rw [Finset.mem_erase] at hM
        obtain ⟨-, hMline⟩ := hM
        simp only [lineFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hMline
        obtain ⟨-, hMfull⟩ := hMline
        rw [Finset.mem_erase] at hzM
        exact by simpa [Pfin] using hMfull (by simpa using hzM.2)
  have htotal : Pfin.card = (s + 1) * (s * t' + 1) := by
    rw [hPfin_eq, Finset.card_union_of_disjoint hdisjN, Finset.card_biUnion]
    · rw [hNcard]
      have hsum : ∑ p ∈ Γ.neighborFinset L0, (C p).card = (s + 1) * (t' * s) := by
        rw [Finset.sum_congr rfl hCcard, Finset.sum_const, smul_eq_mul, hNcard]
      rw [hsum]
      ring
    · exact hdisjC
  rw [show P'.ncard = Pfin.card from Set.ncard_eq_toFinset_card' P']
  exact htotal

theorem ncard_neighborSet_subquadrangleGraph_of_mem_point
    (c : Γ.Coloring (Fin 2)) {P' : Set V}
    {t' : ℕ} (hF : IsFullSubquadrangle c P' t') {x : V} (hx : x ∈ P') :
    ((Γ.induce (subquadrangleSet Γ c P')).neighborSet
      ⟨x, mem_subquadrangleSet.mpr (Or.inl hx)⟩).ncard = t' + 1 := by
  classical
  have h0 : ∀ y ∈ P', c y = 0 := hF.1
  have hcongr := Set.ncard_congr
    (s := {L | Γ.Adj x L ∧ Γ.neighborSet L ⊆ P'})
    (t := (Γ.induce (subquadrangleSet Γ c P')).neighborSet
      ⟨x, mem_subquadrangleSet.mpr (Or.inl hx)⟩)
    (fun L hL => (⟨L, mem_subquadrangleSet.mpr
      (Or.inr (mem_subquadrangleLines.mpr
        ⟨color_eq_one_of_adj_of_color_eq_zero (h0 x hx) hL.1, hL.2⟩))⟩ :
      subquadrangleSet Γ c P'))
    (fun L hL => SimpleGraph.induce_adj.mpr hL.1)
    (fun L L' hL hL' heq => congrArg Subtype.val heq)
    (fun v hv => by
      have hxL : Γ.Adj x v.1 := SimpleGraph.induce_adj.mp hv
      have hLmem : v.1 ∈ subquadrangleLines Γ c P' := by
        rcases (mem_subquadrangleSet.mp v.2) with hvP | hvL
        · exact absurd ((h0 x hx).trans (h0 v.1 hvP).symm) (c.valid hxL)
        · exact hvL
      refine ⟨v.1, ⟨hxL, (mem_subquadrangleLines.mp hLmem).2⟩, ?_⟩
      exact Subtype.ext rfl)
  rw [← hcongr]
  exact hF.2.2.1 x hx

theorem degree_subquadrangleGraph_of_mem_point
    (c : Γ.Coloring (Fin 2)) {P' : Set V}
    {t' : ℕ} (hF : IsFullSubquadrangle c P' t') {x : V} (hx : x ∈ P') :
    (Γ.induce (subquadrangleSet Γ c P')).degree
      ⟨x, mem_subquadrangleSet.mpr (Or.inl hx)⟩ = t' + 1 := by
  rw [← ncard_neighborSet]
  exact ncard_neighborSet_subquadrangleGraph_of_mem_point c hF hx

theorem ncard_neighborSet_subquadrangleGraph_of_mem_line
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {t' : ℕ} {P' : Set V} (hF : IsFullSubquadrangle c P' t')
    {L : V} (hL : L ∈ subquadrangleLines Γ c P') :
    ((Γ.induce (subquadrangleSet Γ c P')).neighborSet
      ⟨L, mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mp hL))⟩).ncard = s + 1 := by
  classical
  have hcongr := Set.ncard_congr
    (s := Γ.neighborSet L)
    (t := (Γ.induce (subquadrangleSet Γ c P')).neighborSet
      ⟨L, mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mp hL))⟩)
    (fun z hz => (⟨z, mem_subquadrangleSet.mpr (Or.inl (hL.2 hz))⟩ :
      subquadrangleSet Γ c P'))
    (fun z hz => SimpleGraph.induce_adj.mpr hz)
    (fun z z' hz hz' heq => congrArg Subtype.val heq)
    (fun v hv => by
      have hLv : Γ.Adj L v.1 := SimpleGraph.induce_adj.mp hv
      exact ⟨v.1, hLv, Subtype.ext rfl⟩)
  rw [← hcongr, ncard_neighborSet, hdeg L, if_neg (by rw [hL.1]; decide)]

theorem degree_subquadrangleGraph_of_mem_line
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {t' : ℕ} {P' : Set V} (hF : IsFullSubquadrangle c P' t')
    {L : V} (hL : L ∈ subquadrangleLines Γ c P') :
    (Γ.induce (subquadrangleSet Γ c P')).degree
      ⟨L, mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mp hL))⟩ = s + 1 := by
  rw [← ncard_neighborSet]
  exact ncard_neighborSet_subquadrangleGraph_of_mem_line c hdeg hF hL

theorem isThick_subquadrangleGraph (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {t' : ℕ} {P' : Set V} (hF : IsFullSubquadrangle c P' t') (ht' : 2 ≤ t') :
    IsThick (Γ.induce (subquadrangleSet Γ c P')) := by
  classical
  intro v
  obtain ⟨x, hxS⟩ := v
  rcases (mem_subquadrangleSet.mp hxS) with hxP | hxL
  · have hdegx := degree_subquadrangleGraph_of_mem_point c hF hxP
    have hv : (⟨x, hxS⟩ : subquadrangleSet Γ c P') =
        ⟨x, mem_subquadrangleSet.mpr (Or.inl hxP)⟩ := Subtype.ext rfl
    rw [hv, hdegx]
    omega
  · have hdegx := degree_subquadrangleGraph_of_mem_line c hdeg hF hxL
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    have hv : (⟨x, hxS⟩ : subquadrangleSet Γ c P') =
        ⟨x, mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mp hxL))⟩ :=
      Subtype.ext rfl
    rw [hv, hdegx]
    omega

end Basic

end CFSG.Geometry.GeneralizedQuadrangles

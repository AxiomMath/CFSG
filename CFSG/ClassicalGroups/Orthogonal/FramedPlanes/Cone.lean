module

public import CFSG.ClassicalGroups.Orthogonal.FramedPlanes.Geometry

public section

namespace CFSG.ClassicalGroups.Orthogonal.FramedPlanes

open Module QuadraticMap

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {ν : F} {n : ℕ}

private lemma finrank_plane_le_two [Module.Finite F V] [CharP F 2] (x : FrameVert Q ν n) :
    finrank F x.plane ≤ 2 := by
  calc
    finrank F x.plane ≤ hullDim Q x.plane := Nat.le_add_right _ _
    _ = 2 := FrameVert.hullDim_plane x

theorem hullDim_sup_plane_le [Module.Finite F V] [CharP F 2] (U : Submodule F V)
    (x : FrameVert Q ν n) : hullDim Q (U ⊔ x.plane) ≤ hullDim Q U + 4 := by
  have h := hullDim_sup_le (Q := Q) U x.plane
  have hx := finrank_plane_le_two x
  omega

theorem hullDim_sup_plane_le_of_le_orthogonal [Module.Finite F V] [CharP F 2]
    {U : Submodule F V} {x : FrameVert Q ν n}
    (h : x.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U) :
    hullDim Q (U ⊔ x.plane) ≤ hullDim Q U + 2 := by
  have h' := hullDim_sup_le_of_le_orthogonal (Q := Q) h
  rw [FrameVert.hullDim_plane x] at h'
  exact h'

private lemma exists_not_mem_of_card_lt {T : Finset (Fin n)} (hT : T.card < n) :
    ∃ t : Fin n, t ∉ T := by
  have hcard : T.card < (Finset.univ : Finset (Fin n)).card := by
    simpa using hT
  obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨t, ht⟩

private lemma span_pair_le {u w : V} {W : Submodule F V} (hu : u ∈ W) (hw : w ∈ W) :
    Submodule.span F {u, w} ≤ W := by
  apply Submodule.span_le.mpr
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact hu
  · exact hw

theorem exists_typ_not_mem_plane_le_orthogonal [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) {U : Submodule F V}
    (hU : hullDim Q U + 3 ≤ finrank F V) {T : Finset (Fin n)} (hT : T.card < n) :
    ∃ z : FrameVert Q ν n, z.typ ∉ T ∧
      z.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U := by
  obtain ⟨u, hu, w, hw, hQu, hQw, huw⟩ :=
    exists_framedPair_orthogonal (Q := Q) hQ hU ν
  obtain ⟨t, ht⟩ := exists_not_mem_of_card_lt hT
  exact ⟨⟨t, u, w, hQu, hQw, huw⟩, ht, span_pair_le hu hw⟩

theorem frameGraph_adj_of_le_orthogonal {x z : FrameVert Q ν n} {U : Submodule F V}
    (hx : x.plane ≤ U) (hz : z.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U)
    (ht : x.typ ≠ z.typ) : (frameGraph Q ν n).Adj x z := by
  refine frameGraph_adj_iff.mpr ⟨ht, ?_⟩
  rw [FrameVert.orth_iff_plane_le_orthogonal]
  exact le_trans hz (LinearMap.BilinForm.orthogonal_le (B := polarBilin Q) hx)

theorem exists_adj_adj [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n)
    (x y : FrameVert Q ν n) :
    ∃ z, (frameGraph Q ν n).Adj x z ∧ (frameGraph Q ν n).Adj y z := by
  have hU : hullDim Q (x.plane ⊔ y.plane) + 3 ≤ finrank F V := by
    have h := hullDim_sup_plane_le (Q := Q) x.plane y
    rw [FrameVert.hullDim_plane x] at h
    omega
  obtain ⟨z, hzt, hzU⟩ :=
    exists_typ_not_mem_plane_le_orthogonal (Q := Q) (hQ := hQ)
      (U := x.plane ⊔ y.plane) (hU := hU) (T := {x.typ, y.typ}) (hT := by
        have h2 : ({x.typ, y.typ} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
        omega)
  have hxz : (frameGraph Q ν n).Adj x z := by
    refine frameGraph_adj_of_le_orthogonal (U := x.plane ⊔ y.plane) le_sup_left hzU ?_
    intro h
    exact hzt (by simp [h])
  have hyz : (frameGraph Q ν n).Adj y z := by
    refine frameGraph_adj_of_le_orthogonal (x := y) (U := x.plane ⊔ y.plane) le_sup_right hzU ?_
    intro h
    exact hzt (by simp [h])
  exact ⟨z, hxz, hyz⟩

theorem frameGraph_preconnected [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n) :
    (frameGraph Q ν n).Preconnected := by
  intro x y
  obtain ⟨z, hxz, hyz⟩ := exists_adj_adj hQ hV hn x y
  exact hxz.reachable.trans hyz.symm.reachable

theorem frameGraph_ediam_le_two [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n) :
    (frameGraph Q ν n).ediam ≤ 2 := by
  refine SimpleGraph.ediam_le_of_edist_le fun x y => ?_
  obtain ⟨z, hxz, hyz⟩ := exists_adj_adj hQ hV hn x y
  let p : (frameGraph Q ν n).Walk x y := .cons hxz (.cons hyz.symm .nil)
  have hp : p.length = 2 := rfl
  exact (SimpleGraph.edist_le p).trans (by rw [hp]; norm_num)

@[expose] def IsGoodPair (x y : FrameVert Q ν n) : Prop :=
  hullDim Q (x.plane ⊔ y.plane) ≤ 4

theorem IsGoodPair.symm {x y : FrameVert Q ν n} (h : IsGoodPair x y) : IsGoodPair y x := by
  change hullDim Q (x.plane ⊔ y.plane) ≤ 4 at h
  change hullDim Q (y.plane ⊔ x.plane) ≤ 4
  rwa [sup_comm] at h

theorem isGoodPair_of_polar_u_eq_zero [Module.Finite F V] [CharP F 2] {z y : FrameVert Q ν n}
    (h₁ : polar Q z.u y.u = 0) (h₂ : polar Q z.u y.w = 0) : IsGoodPair z y :=
  hullDim_span_pair_sup_le_four (Q := Q) (z₁ := z.u) (z₂ := z.w) (p₁ := y.u) (p₂ := y.w)
    (by rw [z.polar_u_w]; exact one_ne_zero)
    (by rw [y.polar_u_w]; exact one_ne_zero) h₁ h₂

theorem isGoodPair_of_polar_w_eq_zero [Module.Finite F V] [CharP F 2] {z y : FrameVert Q ν n}
    (h₁ : polar Q z.w y.u = 0) (h₂ : polar Q z.w y.w = 0) : IsGoodPair z y := by
  have hz : polar Q z.w z.u = 1 := by
    rw [polar_comm Q z.w z.u]
    exact z.polar_u_w
  have h := hullDim_span_pair_sup_le_four (Q := Q) (z₁ := z.w) (z₂ := z.u)
    (p₁ := y.u) (p₂ := y.w) (by rw [hz]; exact one_ne_zero)
    (by rw [y.polar_u_w]; exact one_ne_zero) h₁ h₂
  rw [Set.pair_comm z.w z.u] at h
  exact h

private lemma plane_le_orthogonal_of_adj {p q : FrameVert Q ν n}
    (h : (frameGraph Q ν n).Adj p q) :
    q.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) p.plane :=
  FrameVert.orth_iff_plane_le_orthogonal.mp (frameGraph_adj_iff.mp h).2

private lemma plane_le_orthogonal_sup_of_mem_neighborSet {a c v : FrameVert Q ν n}
    (h : v ∈ (frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c) :
    v.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (a.plane ⊔ c.plane) := by
  intro m hm
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro p hp
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Submodule.mem_sup.mp hp
  have h₁ := plane_le_orthogonal_of_adj h.1
  have h₂ := plane_le_orthogonal_of_adj h.2
  have hm₁ : (polarBilin Q p₁) m = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp (h₁ hm)) p₁ hp₁
  have hm₂ : (polarBilin Q p₂) m = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp (h₂ hm)) p₂ hp₂
  rw [map_add, LinearMap.add_apply, hm₁, hm₂, add_zero]

private lemma adj_of_le_orthogonal_four {a c x y z : FrameVert Q ν n}
    (hz : z.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q)
      ((a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane)))
    (ht : z.typ ∉ ({a.typ, c.typ, x.typ, y.typ} : Finset (Fin n))) :
    (frameGraph Q ν n).Adj a z ∧ (frameGraph Q ν n).Adj c z ∧
      (frameGraph Q ν n).Adj x z ∧ (frameGraph Q ν n).Adj y z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane))
      (le_sup_of_le_left le_sup_left) hz ?_
    intro h
    exact ht (by simp [h])
  · refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane))
      (le_sup_of_le_left le_sup_right) hz ?_
    intro h
    exact ht (by simp [h])
  · refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane))
      (le_sup_of_le_right le_sup_left) hz ?_
    intro h
    exact ht (by simp [h])
  · refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane))
      (le_sup_of_le_right le_sup_right) hz ?_
    intro h
    exact ht (by simp [h])

private lemma reachable_induce_of_isGoodPair [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n)
    {a c x y : FrameVert Q ν n} (hac : IsGoodPair a c)
    (hx : x ∈ (frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c)
    (hy : y ∈ (frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c)
    (hxy : IsGoodPair x y) :
    ((frameGraph Q ν n).induce
      ((frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c)).Reachable
        ⟨x, hx⟩ ⟨y, hy⟩ := by
  have hxac := plane_le_orthogonal_sup_of_mem_neighborSet hx
  have hyac := plane_le_orthogonal_sup_of_mem_neighborSet hy
  have hW : x.plane ⊔ y.plane ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (a.plane ⊔ c.plane) :=
    sup_le hxac hyac
  have hU : hullDim Q ((a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane)) + 3 ≤ finrank F V := by
    have h := hullDim_sup_le_of_le_orthogonal (Q := Q) hW
    have hac' : hullDim Q (a.plane ⊔ c.plane) ≤ 4 := hac
    have hxy' : hullDim Q (x.plane ⊔ y.plane) ≤ 4 := hxy
    omega
  obtain ⟨z, hzt, hzU⟩ :=
    exists_typ_not_mem_plane_le_orthogonal (Q := Q) (hQ := hQ)
      (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane)) (hU := hU)
      (T := {a.typ, c.typ, x.typ, y.typ}) (hT := by
        have h4 : ({a.typ, c.typ, x.typ, y.typ} : Finset (Fin n)).card ≤ 4 :=
          Finset.card_le_four
        omega)
  obtain ⟨hza, hzc, hzx, hzy⟩ := adj_of_le_orthogonal_four hzU hzt
  have hzN : z ∈ (frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c :=
    ⟨hza, hzc⟩
  have hzy' : ((frameGraph Q ν n).induce
      ((frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c)).Adj
        ⟨z, hzN⟩ ⟨y, hy⟩ :=
    SimpleGraph.induce_adj.2 hzy.symm
  exact (SimpleGraph.induce_adj.2 hzx).reachable.trans hzy'.reachable

private lemma exists_framed_pair_orthogonal_four [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V)
    {a c x y : FrameVert Q ν n} (hac : IsGoodPair a c)
    (hxac : x.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (a.plane ⊔ c.plane))
    (hyac : y.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (a.plane ⊔ c.plane)) :
    ∃ z₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
        ((a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane)),
      Q z₁ = 1 ∧
      ∃ w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((a.plane ⊔ c.plane) ⊔ x.plane),
        Q w = ν ∧ polar Q z₁ w = 1 := by
  have hW : x.plane ⊔ y.plane ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (a.plane ⊔ c.plane) :=
    sup_le hxac hyac
  have hUgen : hullDim Q ((a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane)) < finrank F V := by
    have h := hullDim_sup_le_of_le_orthogonal (Q := Q) hW
    have hxy : hullDim Q (x.plane ⊔ y.plane) ≤ 6 := by
      have h2 := hullDim_sup_plane_le (Q := Q) x.plane y
      rw [FrameVert.hullDim_plane x] at h2
      omega
    have hac' : hullDim Q (a.plane ⊔ c.plane) ≤ 4 := hac
    omega
  obtain ⟨z₁, hz₁U, hQz₁, l, hlU, hz₁l⟩ :=
    exists_Q_eq_one_polar_eq_one (Q := Q) hQ hUgen
  have hU'le : (a.plane ⊔ c.plane) ⊔ x.plane ≤
      (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane) :=
    sup_le_sup_left le_sup_left _
  have hlU' : l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
      ((a.plane ⊔ c.plane) ⊔ x.plane) :=
    LinearMap.BilinForm.orthogonal_le (B := polarBilin Q) hU'le hlU
  have hU'3 : hullDim Q ((a.plane ⊔ c.plane) ⊔ x.plane) + 3 ≤ finrank F V := by
    have h := hullDim_sup_plane_le_of_le_orthogonal (Q := Q) hxac
    have hac' : hullDim Q (a.plane ⊔ c.plane) ≤ 4 := hac
    omega
  obtain ⟨w, hwU', hz₁w, hQw⟩ :=
    exists_polar_eq_one_Q_eq (Q := Q) hQ hU'3 hlU' hz₁l ν
  exact ⟨z₁, hz₁U, hQz₁, w, hwU', hQw, hz₁w⟩

private lemma polar_eq_zero_of_mem_orthogonal {z₁ : V} {W : Submodule F V}
    (hz : z₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W)
    {y : FrameVert Q ν n} (hy : y.plane ≤ W) :
    polar Q z₁ y.u = 0 ∧ polar Q z₁ y.w = 0 := by
  have hyu : y.u ∈ W := hy (Submodule.subset_span (by simp))
  have hyw : y.w ∈ W := hy (Submodule.subset_span (by simp))
  constructor
  · rw [polar_comm Q z₁ y.u]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz) y.u hyu
  · rw [polar_comm Q z₁ y.w]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz) y.w hyw

private lemma exists_orthogonal_vertex_isGoodPair [Finite F] [CharP F 2]
    [FiniteDimensional F V] (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V)
    (hn : 5 ≤ n) {a c x y : FrameVert Q ν n} (hac : IsGoodPair a c)
    (hxac : x.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (a.plane ⊔ c.plane))
    (hyac : y.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (a.plane ⊔ c.plane)) :
    ∃ z : FrameVert Q ν n, z.plane ≤
        LinearMap.BilinForm.orthogonal (polarBilin Q) ((a.plane ⊔ c.plane) ⊔ x.plane) ∧
      z.typ ∉ ({a.typ, c.typ, x.typ} : Finset (Fin n)) ∧ IsGoodPair z y := by
  obtain ⟨z₁, hz₁U, hQz₁, w, hwU', hQw, hz₁w⟩ :=
    exists_framed_pair_orthogonal_four hQ hV hac hxac hyac
  have hz₁U' : z₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
      ((a.plane ⊔ c.plane) ⊔ x.plane) :=
    LinearMap.BilinForm.orthogonal_le (B := polarBilin Q)
      (sup_le_sup_left le_sup_left _) hz₁U
  obtain ⟨t, ht⟩ := exists_not_mem_of_card_lt (T := {a.typ, c.typ, x.typ}) (by
    have h3 : ({a.typ, c.typ, x.typ} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    omega)
  let z : FrameVert Q ν n := ⟨t, z₁, w, hQz₁, hQw, hz₁w⟩
  have hzU' : z.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q)
      ((a.plane ⊔ c.plane) ⊔ x.plane) :=
    span_pair_le hz₁U' hwU'
  obtain ⟨hz₁yu, hz₁yw⟩ :=
    polar_eq_zero_of_mem_orthogonal (y := y) hz₁U (le_sup_of_le_right le_sup_right)
  refine ⟨z, hzU', ht, isGoodPair_of_polar_u_eq_zero (z := z) (y := y) ?_ ?_⟩
  · change polar Q z₁ y.u = 0
    exact hz₁yu
  · change polar Q z₁ y.w = 0
    exact hz₁yw

private lemma exists_common_neighbor_isGoodPair [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n)
    {a c x y : FrameVert Q ν n} (hac : IsGoodPair a c)
    (hx : x ∈ (frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c)
    (hy : y ∈ (frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c) :
    ∃ z, z ∈ (frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c ∧
      (frameGraph Q ν n).Adj x z ∧ IsGoodPair z y := by
  have hxac := plane_le_orthogonal_sup_of_mem_neighborSet hx
  have hyac := plane_le_orthogonal_sup_of_mem_neighborSet hy
  obtain ⟨z, hzU', hzt, hzy⟩ :=
    exists_orthogonal_vertex_isGoodPair hQ hV hn hac hxac hyac
  have hza : (frameGraph Q ν n).Adj a z := by
    refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ x.plane)
      (le_sup_of_le_left le_sup_left) hzU' ?_
    intro h
    exact hzt (Finset.mem_insert.mpr (Or.inl h.symm))
  have hzc : (frameGraph Q ν n).Adj c z := by
    refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ x.plane)
      (le_sup_of_le_left le_sup_right) hzU' ?_
    intro h
    exact hzt (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inl h.symm))))
  have hzx : (frameGraph Q ν n).Adj x z := by
    refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ x.plane)
      le_sup_right hzU' ?_
    intro h
    exact hzt (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h.symm)))))
  exact ⟨z, ⟨hza, hzc⟩, hzx, hzy⟩

theorem preconnected_induce_neighborSet_inter [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n)
    {a c : FrameVert Q ν n} (h : IsGoodPair a c) :
    ((frameGraph Q ν n).induce
      ((frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c)).Preconnected := by
  intro x y
  obtain ⟨z, hzN, hxz, hzy⟩ := exists_common_neighbor_isGoodPair hQ hV hn h x.2 y.2
  have hxz' : ((frameGraph Q ν n).induce
      ((frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c)).Adj
        ⟨x, x.2⟩ ⟨z, hzN⟩ :=
    SimpleGraph.induce_adj.2 hxz
  have hzy' : ((frameGraph Q ν n).induce
      ((frameGraph Q ν n).neighborSet a ∩ (frameGraph Q ν n).neighborSet c)).Reachable
        ⟨z, hzN⟩ ⟨y, y.2⟩ :=
    reachable_induce_of_isGoodPair hQ hV hn h hzN y.2 hzy
  exact hxz'.reachable.trans hzy'

end CFSG.ClassicalGroups.Orthogonal.FramedPlanes

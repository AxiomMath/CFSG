module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.FrameGeometry
public import CFSG.Mathlib.LinearAlgebra.QuadraticForm.HullDim

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

open _root_.QuadraticMap CFSG.QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hullDim_plane (x : FrameVert) : hullDim (Q 6) x.plane = 2 :=
  hullDim_span_pair x.polar_u_w

private lemma plane_le_orthogonal_of_adj {p q : FrameVert} (h : frameGraph.Adj p q) :
    q.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) p.plane :=
  FrameVert.orth_iff_plane_le_orthogonal.mp (frameGraph_adj_iff.mp h).2

private lemma plane_le_orthogonal_sup_of_mem_neighborSet {a c v : FrameVert}
    (h : v ∈ frameGraph.neighborSet a ∩ frameGraph.neighborSet c) :
    v.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) (a.plane ⊔ c.plane) := by
  rw [orthogonal_sup]
  exact le_inf (plane_le_orthogonal_of_adj h.1) (plane_le_orthogonal_of_adj h.2)

private lemma finrank_plane_le_two (x : FrameVert) : Module.finrank (ZMod 2) x.plane ≤ 2 := by
  calc
    Module.finrank (ZMod 2) x.plane ≤ hullDim (Q 6) x.plane := Nat.le_add_right _ _
    _ = 2 := hullDim_plane x

theorem hullDim_sup_plane_le (U : Submodule (ZMod 2) (V 6)) (x : FrameVert) :
    hullDim (Q 6) (U ⊔ x.plane) ≤ hullDim (Q 6) U + 4 := by
  have h := hullDim_sup_le (Q := Q 6) U x.plane
  have hx := finrank_plane_le_two x
  omega

theorem hullDim_sup_plane_le_of_le_orthogonal {U : Submodule (ZMod 2) (V 6)} {x : FrameVert}
    (h : x.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) U) :
    hullDim (Q 6) (U ⊔ x.plane) ≤ hullDim (Q 6) U + 2 := by
  have h' := hullDim_sup_le_of_le_orthogonal (Q := Q 6) h
  rw [hullDim_plane x] at h'
  exact h'

theorem exists_typ_not_mem_plane_le_orthogonal {U : Submodule (ZMod 2) (V 6)}
    (hU : hullDim (Q 6) U ≤ 9) {T : Finset (Fin 5)} (hT : T.card ≤ 4) :
    ∃ z : FrameVert, z.typ ∉ T ∧
      z.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) U := by
  have hUle : hullDim (Q 6) U ≤ 9 := hU
  have hTle : T.card ≤ 4 := hT
  have hV : Module.finrank (ZMod 2) (V 6) = 12 := by
    simp
  obtain ⟨u, hu, w, hw, hQu, hQw, huw⟩ :=
    exists_framedPair_orthogonal (Q := Q 6) (U := U) (nondegenerate_Q 6)
      (by rw [hV]; omega)
  obtain ⟨t, ht⟩ : ∃ t : Fin 5, t ∉ T := by
    have hcard : T.card < (Finset.univ : Finset (Fin 5)).card := by
      have h5 : (Finset.univ : Finset (Fin 5)).card = 5 := by simp
      omega
    obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨t, ht⟩
  refine ⟨⟨t, u, w, hQu, hQw, huw⟩, ht, ?_⟩
  apply Submodule.span_le.mpr
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact hu
  · exact hw

theorem frameGraph_adj_of_le_orthogonal {x z : FrameVert} {U : Submodule (ZMod 2) (V 6)}
    (hx : x.plane ≤ U) (hz : z.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) U)
    (ht : x.typ ≠ z.typ) : frameGraph.Adj x z := by
  refine frameGraph_adj_iff.mpr ⟨ht, ?_⟩
  rw [FrameVert.orth_iff_plane_le_orthogonal]
  exact le_trans hz (LinearMap.BilinForm.orthogonal_le (B := polarBilin (Q 6)) hx)

theorem exists_adj_adj (x y : FrameVert) : ∃ z, frameGraph.Adj x z ∧ frameGraph.Adj y z := by
  have hU : hullDim (Q 6) (x.plane ⊔ y.plane) ≤ 9 := by
    have h := hullDim_sup_plane_le x.plane y
    rw [hullDim_plane x] at h
    omega
  obtain ⟨z, hzt, hzU⟩ :=
    exists_typ_not_mem_plane_le_orthogonal (U := x.plane ⊔ y.plane) hU
      (T := {x.typ, y.typ}) (hT := Finset.card_le_two.trans (by norm_num))
  have hxz : frameGraph.Adj x z := by
    refine frameGraph_adj_of_le_orthogonal (U := x.plane ⊔ y.plane) le_sup_left hzU ?_
    intro h
    exact hzt (by simp [h])
  have hyz : frameGraph.Adj y z := by
    refine frameGraph_adj_of_le_orthogonal (x := y) (U := x.plane ⊔ y.plane) le_sup_right hzU ?_
    intro h
    exact hzt (by simp [h])
  exact ⟨z, hxz, hyz⟩

theorem frameGraph_connected : frameGraph.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun x y => ?_, ⟨stdVert 0 0⟩⟩
  obtain ⟨z, hxz, hyz⟩ := exists_adj_adj x y
  exact hxz.reachable.trans hyz.symm.reachable

theorem frameGraph_ediam_le_two : frameGraph.ediam ≤ 2 := by
  refine SimpleGraph.ediam_le_of_edist_le fun x y => ?_
  obtain ⟨z, hxz, hyz⟩ := exists_adj_adj x y
  let p : frameGraph.Walk x y := .cons hxz (.cons hyz.symm .nil)
  have hp : p.length = 2 := rfl
  exact (SimpleGraph.edist_le p).trans (by rw [hp]; norm_num)

@[expose] def IsGoodPair (x y : FrameVert) : Prop :=
  hullDim (Q 6) (x.plane ⊔ y.plane) ≤ 4

theorem IsGoodPair.symm {x y : FrameVert} (h : IsGoodPair x y) : IsGoodPair y x := by
  change hullDim (Q 6) (x.plane ⊔ y.plane) ≤ 4 at h
  change hullDim (Q 6) (y.plane ⊔ x.plane) ≤ 4
  rwa [sup_comm] at h

theorem isGoodPair_of_polar_u_eq_zero {z y : FrameVert} (h₁ : polar (Q 6) z.u y.u = 0)
    (h₂ : polar (Q 6) z.u y.w = 0) : IsGoodPair z y :=
  hullDim_span_pair_sup_le_four (Q := Q 6) z.polar_u_w y.polar_u_w h₁ h₂

theorem isGoodPair_of_polar_w_eq_zero {z y : FrameVert} (h₁ : polar (Q 6) z.w y.u = 0)
    (h₂ : polar (Q 6) z.w y.w = 0) : IsGoodPair z y := by
  have hz : polar (Q 6) z.w z.u = 1 := by
    rw [polar_comm (Q 6) z.w z.u]
    exact z.polar_u_w
  have h := hullDim_span_pair_sup_le_four (Q := Q 6) hz y.polar_u_w h₁ h₂
  rw [Set.pair_comm z.w z.u] at h
  exact h

private lemma reachable_induce_of_isGoodPair {a c x y : FrameVert} (hac : IsGoodPair a c)
    (hx : x ∈ frameGraph.neighborSet a ∩ frameGraph.neighborSet c)
    (hy : y ∈ frameGraph.neighborSet a ∩ frameGraph.neighborSet c) (hxy : IsGoodPair x y) :
    (frameGraph.induce (frameGraph.neighborSet a ∩ frameGraph.neighborSet c)).Reachable
      ⟨x, hx⟩ ⟨y, hy⟩ := by
  have hac' : hullDim (Q 6) (a.plane ⊔ c.plane) ≤ 4 := hac
  have hxy' : hullDim (Q 6) (x.plane ⊔ y.plane) ≤ 4 := hxy
  have hxac := plane_le_orthogonal_sup_of_mem_neighborSet hx
  have hyac := plane_le_orthogonal_sup_of_mem_neighborSet hy
  have hW : x.plane ⊔ y.plane ≤
      LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) (a.plane ⊔ c.plane) :=
    sup_le hxac hyac
  have hU : hullDim (Q 6) ((a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane)) ≤ 9 := by
    have h := hullDim_sup_le_of_le_orthogonal (Q := Q 6) hW
    omega
  obtain ⟨z, hzt, hzU⟩ :=
    exists_typ_not_mem_plane_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane))
      hU (T := {a.typ, c.typ, x.typ, y.typ}) (hT := Finset.card_le_four)
  have hza : frameGraph.Adj a z := by
    refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane))
      (le_sup_of_le_left le_sup_left) hzU ?_
    intro h
    exact hzt (by simp [h])
  have hzc : frameGraph.Adj c z := by
    refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane))
      (le_sup_of_le_left le_sup_right) hzU ?_
    intro h
    exact hzt (by simp [h])
  have hzx : frameGraph.Adj x z := by
    refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane))
      (le_sup_of_le_right le_sup_left) hzU ?_
    intro h
    exact hzt (by simp [h])
  have hzy : frameGraph.Adj y z := by
    refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane))
      (le_sup_of_le_right le_sup_right) hzU ?_
    intro h
    exact hzt (by simp [h])
  have hzN : z ∈ frameGraph.neighborSet a ∩ frameGraph.neighborSet c := ⟨hza, hzc⟩
  have hzy' : (frameGraph.induce (frameGraph.neighborSet a ∩ frameGraph.neighborSet c)).Adj
      ⟨z, hzN⟩ ⟨y, hy⟩ :=
    SimpleGraph.induce_adj.2 hzy.symm
  exact (SimpleGraph.induce_adj.2 hzx).reachable.trans hzy'.reachable

private lemma exists_framed_pair_orthogonal_four {a c x y : FrameVert} (hac : IsGoodPair a c)
    (hxac : x.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) (a.plane ⊔ c.plane))
    (hyac : y.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) (a.plane ⊔ c.plane)) :
    ∃ z₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin (Q 6))
        ((a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane)),
      Q 6 z₁ = 1 ∧
      ∃ w ∈ LinearMap.BilinForm.orthogonal (polarBilin (Q 6))
          ((a.plane ⊔ c.plane) ⊔ x.plane),
        Q 6 w = 1 ∧ polar (Q 6) z₁ w = 1 := by
  have hac' : hullDim (Q 6) (a.plane ⊔ c.plane) ≤ 4 := hac
  have hW : x.plane ⊔ y.plane ≤
      LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) (a.plane ⊔ c.plane) :=
    sup_le hxac hyac
  have hUgen : hullDim (Q 6) ((a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane)) <
      Module.finrank (ZMod 2) (V 6) := by
    have h := hullDim_sup_le_of_le_orthogonal (Q := Q 6) hW
    have hxy : hullDim (Q 6) (x.plane ⊔ y.plane) ≤ 6 := by
      have h2 := hullDim_sup_plane_le x.plane y
      rw [hullDim_plane x] at h2
      omega
    have hV : Module.finrank (ZMod 2) (V 6) = 12 := by
      simp
    rw [hV]
    omega
  obtain ⟨z₁, hz₁U, hQz₁, l, hlU, hz₁l⟩ :=
    exists_Q_eq_one_polar_eq_one (Q := Q 6)
      (U := (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane)) (nondegenerate_Q 6) hUgen
  have hU' : hullDim (Q 6) ((a.plane ⊔ c.plane) ⊔ x.plane) ≤ 6 := by
    have h := hullDim_sup_le_of_le_orthogonal (Q := Q 6) hxac
    rw [hullDim_plane x] at h
    omega
  have hU'le : (a.plane ⊔ c.plane) ⊔ x.plane ≤
      (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane) :=
    sup_le_sup_left le_sup_left _
  have hlU' : l ∈ LinearMap.BilinForm.orthogonal (polarBilin (Q 6))
      ((a.plane ⊔ c.plane) ⊔ x.plane) :=
    LinearMap.BilinForm.orthogonal_le (B := polarBilin (Q 6)) hU'le hlU
  have hU'3 : hullDim (Q 6) ((a.plane ⊔ c.plane) ⊔ x.plane) + 3 ≤
      Module.finrank (ZMod 2) (V 6) := by
    have hV : Module.finrank (ZMod 2) (V 6) = 12 := by
      simp
    rw [hV]
    omega
  obtain ⟨w, hwU', hz₁w, hQw⟩ :=
    exists_polar_eq_one_Q_eq_one (Q := Q 6) (U := (a.plane ⊔ c.plane) ⊔ x.plane)
      (nondegenerate_Q 6) hU'3 hlU' hz₁l
  exact ⟨z₁, hz₁U, hQz₁, w, hwU', hQw, hz₁w⟩

private lemma exists_common_neighbor_isGoodPair {a c x y : FrameVert} (hac : IsGoodPair a c)
    (hx : x ∈ frameGraph.neighborSet a ∩ frameGraph.neighborSet c)
    (hy : y ∈ frameGraph.neighborSet a ∩ frameGraph.neighborSet c) :
    ∃ z, z ∈ frameGraph.neighborSet a ∩ frameGraph.neighborSet c ∧
      frameGraph.Adj x z ∧ IsGoodPair z y := by
  have hxac := plane_le_orthogonal_sup_of_mem_neighborSet hx
  have hyac := plane_le_orthogonal_sup_of_mem_neighborSet hy
  obtain ⟨z₁, hz₁U, hQz₁, w, hwU', hQw, hz₁w⟩ :=
    exists_framed_pair_orthogonal_four hac hxac hyac
  have hU'le : (a.plane ⊔ c.plane) ⊔ x.plane ≤
      (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane) :=
    sup_le_sup_left le_sup_left _
  have hz₁U' : z₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin (Q 6))
      ((a.plane ⊔ c.plane) ⊔ x.plane) :=
    LinearMap.BilinForm.orthogonal_le (B := polarBilin (Q 6)) hU'le hz₁U
  obtain ⟨t, ht⟩ : ∃ t : Fin 5, t ∉ ({a.typ, c.typ, x.typ} : Finset (Fin 5)) := by
    have h3 : ({a.typ, c.typ, x.typ} : Finset (Fin 5)).card ≤ 3 := Finset.card_le_three
    have hcard : ({a.typ, c.typ, x.typ} : Finset (Fin 5)).card <
        (Finset.univ : Finset (Fin 5)).card := by
      have h5 : (Finset.univ : Finset (Fin 5)).card = 5 := by simp
      omega
    obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨t, ht⟩
  let z : FrameVert := ⟨t, z₁, w, hQz₁, hQw, hz₁w⟩
  have hzU' : z.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6))
      ((a.plane ⊔ c.plane) ⊔ x.plane) := by
    apply Submodule.span_le.mpr
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hz₁U'
    · exact hwU'
  have hza : frameGraph.Adj a z := by
    refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ x.plane)
      (le_sup_of_le_left le_sup_left) hzU' ?_
    intro h
    exact ht (Finset.mem_insert.mpr (Or.inl h.symm))
  have hzc : frameGraph.Adj c z := by
    refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ x.plane)
      (le_sup_of_le_left le_sup_right) hzU' ?_
    intro h
    exact ht (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inl h.symm))))
  have hzx : frameGraph.Adj x z := by
    refine frameGraph_adj_of_le_orthogonal (U := (a.plane ⊔ c.plane) ⊔ x.plane)
      le_sup_right hzU' ?_
    intro h
    exact ht (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h.symm)))))
  have hyU : y.plane ≤ (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane) :=
    le_sup_of_le_right le_sup_right
  have hyuU : y.u ∈ (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane) :=
    hyU (Submodule.subset_span (by simp))
  have hywU : y.w ∈ (a.plane ⊔ c.plane) ⊔ (x.plane ⊔ y.plane) :=
    hyU (Submodule.subset_span (by simp))
  have hz₁yu : polar (Q 6) z₁ y.u = 0 := by
    rw [polar_comm (Q 6) z₁ y.u]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz₁U) y.u hyuU
  have hz₁yw : polar (Q 6) z₁ y.w = 0 := by
    rw [polar_comm (Q 6) z₁ y.w]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz₁U) y.w hywU
  have hzy : IsGoodPair z y :=
    isGoodPair_of_polar_u_eq_zero (z := z) (y := y)
      (by
        change polar (Q 6) z₁ y.u = 0
        exact hz₁yu)
      (by
        change polar (Q 6) z₁ y.w = 0
        exact hz₁yw)
  exact ⟨z, ⟨hza, hzc⟩, hzx, hzy⟩

theorem preconnected_induce_neighborSet_inter {a c : FrameVert} (h : IsGoodPair a c) :
    (frameGraph.induce (frameGraph.neighborSet a ∩ frameGraph.neighborSet c)).Preconnected := by
  intro x y
  obtain ⟨z, hzN, hxz, hzy⟩ := exists_common_neighbor_isGoodPair h x.2 y.2
  have hxz' : (frameGraph.induce (frameGraph.neighborSet a ∩ frameGraph.neighborSet c)).Adj
      ⟨x, x.2⟩ ⟨z, hzN⟩ :=
    SimpleGraph.induce_adj.2 hxz
  have hzy' : (frameGraph.induce (frameGraph.neighborSet a ∩ frameGraph.neighborSet c)).Reachable
      ⟨z, hzN⟩ ⟨y, y.2⟩ :=
    reachable_induce_of_isGoodPair h hzN y.2 hzy
  exact hxz'.reachable.trans hzy'

end CFSG.ClassicalGroups.Orthogonal.SixPlane

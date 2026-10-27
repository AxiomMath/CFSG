module

public import CFSG.Geometry.GeneralizedQuadrangles.LinearSpace
public import CFSG.Quasithin.Recognition.Stroth.WeissMoufang

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin
open CFSG.Quasithin.Stroth

universe u v

variable {V : Type u} {Γ : SimpleGraph V} {H : Type v} [Group H] [MulAction H V]
  [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

private theorem propertyH_forward (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) {u x y z : V}
    (hux : Γ.dist u x = 2) (huy : Γ.dist u y = 2) (huz : Γ.dist u z = 2)
    (hxy : Γ.dist x y = 4) (hyz : Γ.dist y z = 4) (hxz : Γ.dist x z = 4)
    (hxcl : x ∈ clSet Γ y z) : y ∈ clSet Γ x z := by
  classical
  have hyx : Γ.dist y x = 4 := by rw [SimpleGraph.dist_comm]; exact hxy
  have hzx : Γ.dist z x = 4 := by rw [SimpleGraph.dist_comm]; exact hxz
  obtain ⟨w, hw_mem, hLxw⟩ :=
    (mem_clSet_iff_line_meets_span hP hT (u := u) (x := y) (y := z) (z := x)
      huy huz hux hyz hyx hzx).mp hxcl
  by_cases hwx : w = x
  · have hx_mem : x ∈ spanSet Γ y z := hwx ▸ hw_mem
    have hxz_ne : x ≠ z := by
      intro h
      rw [h] at hxz
      simp at hxz
    obtain ⟨-, hspan, -⟩ :=
      span_eq_of_mem hP hT hyz hx_mem (right_mem_spanSet hyz) hxz_ne
    rw [mem_clSet]
    exact ⟨y, by rw [hspan]; exact left_mem_spanSet hyz, by simp⟩
  · let Lx : V := commonNeighbor hP hux
    have hLxu : Γ.Adj u Lx := by
      simpa [Lx] using commonNeighbor_adj_left hP hux
    have hLxx : Γ.Adj x Lx := by
      simpa [Lx] using commonNeighbor_adj_right hP hux
    have hLxw : Γ.Adj Lx w := by
      simpa [Lx] using hLxw
    have hu_trace : u ∈ traceSet Γ y z :=
      ⟨by rw [SimpleGraph.dist_comm]; exact huy, by rw [SimpleGraph.dist_comm]; exact huz⟩
    have hwu : w ≠ u := by
      intro h
      exact not_mem_spanSet_of_mem_traceSet hP hT hyz hu_trace (h ▸ hw_mem)
    have hxu : x ≠ u := by
      intro h
      rw [h] at hux
      simp at hux
    have hwz : w ≠ z := by
      intro h
      have hLxz : Γ.Adj Lx z := h ▸ hLxw
      have h1 : Γ.dist x Lx = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hLxx
      have h2 : Γ.dist Lx z = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hLxz
      have htri := hP.connected.dist_triangle (u := x) (v := Lx) (w := z)
      omega
    let Lz : V := commonNeighbor hP huz
    have hLzu : Γ.Adj u Lz := by
      simpa [Lz] using commonNeighbor_adj_left hP huz
    have hLzz : Γ.Adj z Lz := by
      simpa [Lz] using commonNeighbor_adj_right hP huz
    have hLz_ne_Lx : Lz ≠ Lx := by
      intro h
      have hLxz : Γ.Adj Lx z := by
        rw [← h]
        exact hLzz.symm
      have h1 : Γ.dist x Lx = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hLxx
      have h2 : Γ.dist Lx z = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hLxz
      have htri := hP.connected.dist_triangle (u := x) (v := Lx) (w := z)
      omega
    have hzu_ne : z ≠ u := by
      intro h
      rw [h] at huz
      simp at huz
    have hzmem : Lz ∈ Γ.neighborFinset z := by
      rw [mem_neighborFinset]
      exact hLzz
    have hzpos : 0 < ((Γ.neighborFinset z).erase Lz).card := by
      rw [Finset.card_erase_of_mem hzmem, card_neighborFinset_eq_degree]
      have h3 := hT z
      omega
    obtain ⟨p0, hp0⟩ := Finset.card_pos.mp hzpos
    rw [Finset.mem_erase, mem_neighborFinset] at hp0
    obtain ⟨hp0ne, hzp0⟩ := hp0
    let q1 : GPath Γ 1 := GPath.ofAdj hLxu
    let q2 : GPath Γ 2 := GPath.cons Lz q1 hLzu.symm
    let q3 : GPath Γ 3 := GPath.cons z q2 hLzz
    let q4 : GPath Γ 4 := GPath.cons p0 q3 hzp0.symm
    have hq1_0 : q1 0 = u := by simp [q1]
    have hq1_1 : q1 1 = Lx := by simp [q1]
    have hq2_1 : q2 1 = u := by rfl
    have hq3_1 : q3 1 = Lz := by rfl
    have hq4_1 : q4 1 = z := by rfl
    have hq4_2 : q4 2 = Lz := by rfl
    have hq4_3 : q4 3 = u := by rfl
    have hq4_4 : q4 4 = Lx := by rfl
    have hq1_nb : q1.NoBack := by
      intro i hi
      omega
    have hq2_nb : q2.NoBack := by
      refine GPath.noBack_cons Lz q1 hLzu.symm hq1_nb ?_
      rw [hq1_1]
      exact hLz_ne_Lx
    have hq3_nb : q3.NoBack := by
      refine GPath.noBack_cons z q2 hLzz hq2_nb ?_
      rw [hq2_1]
      exact hzu_ne
    have hq4_nb : q4.NoBack := by
      refine GPath.noBack_cons p0 q3 hzp0.symm hq3_nb ?_
      rw [hq3_1]
      exact hp0ne
    obtain ⟨θ, hθfix, hθw⟩ :=
      hM q4 hq4_nb w x (by rw [hq4_4]; exact hLxw)
        (by rw [hq4_4]; exact hLxx.symm)
        (by rw [hq4_3]; exact hwu)
        (by rw [hq4_3]; exact hxu)
    have hθz : θ • z = z :=
      hθfix 2 (by omega) (by omega) z (by rw [hq4_2]; exact hLzz.symm)
    let Ly : V := commonNeighbor hP huy
    have huLy : Γ.Adj u Ly := by
      simpa [Ly] using commonNeighbor_adj_left hP huy
    have hyLy : Γ.Adj y Ly := by
      simpa [Ly] using commonNeighbor_adj_right hP huy
    have hθLy : θ • Ly = Ly :=
      hθfix 3 (by omega) (by omega) Ly (by rw [hq4_3]; exact huLy)
    have hAdj : Γ.Adj Ly (θ • y) := by
      have h' : Γ.Adj (θ • Ly) (θ • y) := (GraphAction.adj_smul θ Ly y).mpr hyLy.symm
      rwa [hθLy] at h'
    have hdist : Γ.dist y (θ • y) ≤ 2 := by
      have htri := hP.connected.dist_triangle (u := y) (v := Ly) (w := θ • y)
      have h1 : Γ.dist y Ly = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyLy
      have h2 : Γ.dist Ly (θ • y) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hAdj
      omega
    obtain ⟨-, hspan_wz, -⟩ :=
      span_eq_of_mem hP hT hyz hw_mem (right_mem_spanSet hyz) hwz
    have hy_wz : y ∈ spanSet Γ w z := by
      rw [hspan_wz]
      exact left_mem_spanSet hyz
    have hmem_xz : θ • y ∈ spanSet Γ x z := by
      intro b hb
      have hb1 : Γ.dist w (θ⁻¹ • b) = 2 := by
        have h := GPath.dist_smul hP.connected θ w (θ⁻¹ • b)
        simpa [hθw, hb.1] using h.symm
      have hb2 : Γ.dist z (θ⁻¹ • b) = 2 := by
        have h := GPath.dist_smul hP.connected θ z (θ⁻¹ • b)
        simpa [hθz, hb.2] using h.symm
      have hble : Γ.dist y (θ⁻¹ • b) ≤ 2 :=
        hy_wz (θ⁻¹ • b) ⟨hb1, hb2⟩
      calc
        Γ.dist (θ • y) b = Γ.dist y (θ⁻¹ • b) := by
          simpa using (GPath.dist_smul hP.connected θ y (θ⁻¹ • b))
        _ ≤ 2 := hble
    rw [mem_clSet]
    exact ⟨θ • y, hmem_xz, hdist⟩

theorem hasPropertyH (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) (u : V) : HasPropertyH Γ u := by
  intro x y z hux huy huz hxy hyz hxz
  constructor
  · intro hzcl
    have h := propertyH_forward hP hT hM (u := u) (x := z) (y := x) (z := y)
      huz hux huy (by rw [SimpleGraph.dist_comm]; exact hxz) hxy
      (by rw [SimpleGraph.dist_comm]; exact hyz) hzcl
    rwa [clSet_comm z y] at h
  · intro hxcl
    have hxcl' : x ∈ clSet Γ z y := by
      rwa [clSet_comm y z] at hxcl
    exact propertyH_forward hP hT hM (u := u) (x := x) (y := z) (z := y)
      hux huz huy hxz (by rw [SimpleGraph.dist_comm]; exact hyz) hxy hxcl'

end CFSG.Geometry.GeneralizedQuadrangles

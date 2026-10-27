module

public import CFSG.Geometry.GeneralizedQuadrangles.Basic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin

universe u v

variable {V : Type u}

section Projection

variable {Γ : SimpleGraph V} {H : Type v} [Group H] [MulAction H V] [GraphAction H Γ]

theorem line_fixed_of_fix_of_fix [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) {θ : H} {y z M : V}
    (hy : θ • y = y) (hz : θ • z = z) (hyM : Γ.Adj y M) (hzM : Γ.Adj M z)
    (hzy : z ≠ y) : θ • M = M := by
  have hyz : Γ.dist y z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hyM hzM hzy.symm
  have hθM : Γ.Adj y (θ • M) := by
    have h := (GraphAction.adj_smul θ y M).mpr hyM
    rwa [hy] at h
  have hθMz : Γ.Adj z (θ • M) := by
    have h := (GraphAction.adj_smul θ M z).mpr hzM
    rw [hz] at h
    exact h.symm
  exact (existsUnique_commonNeighbor hP hyz).unique ⟨hθM, hθMz⟩ ⟨hyM, hzM.symm⟩

theorem all_lines_fixed_of_fix_of_opposite [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) {θ : H} {u w : V}
    (huN : ∀ N, Γ.Adj u N → θ • N = N) (hw : θ • w = w) (huw : Γ.dist u w = 4) :
    ∀ L, Γ.Adj w L → θ • L = L := by
  intro L hwL
  have hwu : Γ.dist w u = 4 := by rw [SimpleGraph.dist_comm]; exact huw
  have huL : Γ.dist u L = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP hwu hwL
  let v : V := proj hP huL
  have hvL : Γ.Adj L v := proj_adj hP huL
  have huv : Γ.dist u v = 2 := proj_dist hP huL
  let N : V := commonNeighbor hP huv
  have huN' : Γ.Adj u N := commonNeighbor_adj_left hP huv
  have hvN : Γ.Adj v N := commonNeighbor_adj_right hP huv
  have hNfix : θ • N = N := huN N huN'
  have hwN : Γ.dist w N = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP huw huN'
  have hwv : Γ.dist w v = 2 := by
    have hwne : w ≠ v := by
      intro h
      rw [h] at huw
      omega
    exact dist_eq_two_of_adj_of_adj_of_ne hP hwL hvL hwne
  have hvproj : v = proj hP hwN :=
    eq_proj hP hwN hvN.symm hwv
  have hθvN : Γ.Adj N (θ • v) := by
    have h := (GraphAction.adj_smul θ v N).mpr hvN
    rw [hNfix] at h
    exact h.symm
  have hwθv : Γ.dist w (θ • v) = 2 := by
    have h := GPath.dist_smul hP.connected θ w v
    rw [hw] at h
    exact h.trans hwv
  have hθv : θ • v = v :=
    (eq_proj hP hwN hθvN hwθv).trans hvproj.symm
  have hvw : Γ.dist v w = 2 := by rw [SimpleGraph.dist_comm]; exact hwv
  have hLcommon : Γ.Adj v L ∧ Γ.Adj w L := ⟨hvL.symm, hwL⟩
  have hθLcommon : Γ.Adj v (θ • L) ∧ Γ.Adj w (θ • L) := by
    refine ⟨?_, ?_⟩
    · have h := (GraphAction.adj_smul θ v L).mpr hvL.symm
      rwa [hθv] at h
    · have h := (GraphAction.adj_smul θ w L).mpr hwL
      rwa [hw] at h
  exact (existsUnique_commonNeighbor hP hvw).unique hθLcommon hLcommon

end Projection

section Trace

variable {Γ : SimpleGraph V} {H : Type v} [Group H] [MulAction H V] [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

theorem smul_eq_of_mem_traceSet (hP : IsGeneralizedPolygon Γ 4) {θ : H} {p y a : V}
    (hpN : ∀ L, Γ.Adj p L → θ • L = L) (hyN : ∀ L, Γ.Adj y L → θ • L = L)
    (hpy : Γ.dist p y = 4) (ha : a ∈ traceSet Γ p y) : θ • a = a := by
  have hpa : Γ.dist p a = 2 := ha.1
  have hya : Γ.dist y a = 2 := ha.2
  let N : V := commonNeighbor hP hpa
  let K : V := commonNeighbor hP hya
  have hpN' : Γ.Adj p N := commonNeighbor_adj_left hP hpa
  have haN : Γ.Adj a N := commonNeighbor_adj_right hP hpa
  have hyK' : Γ.Adj y K := commonNeighbor_adj_left hP hya
  have haK : Γ.Adj a K := commonNeighbor_adj_right hP hya
  have hNfix : θ • N = N := hpN N hpN'
  have hKfix : θ • K = K := hyN K hyK'
  have hNK : N ≠ K := by
    intro h
    have hpy' : Γ.dist p y ≤ 2 := by
      have h1 : Γ.Adj p N := hpN'
      have h2 : Γ.Adj y K := hyK'
      rw [← h] at h2
      have hle := hP.connected.dist_triangle (u := p) (v := N) (w := y)
      have d1 : Γ.dist p N = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h1
      have d2 : Γ.dist N y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h2.symm
      omega
    omega
  have hdistNK : Γ.dist N K = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP haN.symm haK hNK
  have hθaN : Γ.Adj N (θ • a) := by
    have h := (GraphAction.adj_smul θ N a).mpr haN.symm
    rwa [hNfix] at h
  have hθaK : Γ.Adj K (θ • a) := by
    have h := (GraphAction.adj_smul θ K a).mpr haK.symm
    rwa [hKfix] at h
  exact (existsUnique_commonNeighbor hP hdistNK).unique ⟨hθaN, hθaK⟩ ⟨haN.symm, haK.symm⟩

end Trace

section Closure

variable {Γ : SimpleGraph V} {H : Type v} [Group H] [MulAction H V] [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

theorem whorl_projection_data (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {p y z M : V} (hp : c p = 0) {θ : H}
    (hθ : θ ∈ whorlGroup H Γ p) (hy : Γ.dist p y = 4)
    (hyM : Γ.Adj y M) (hzM : Γ.Adj M z) (hzy : z ≠ y) (hzp : Γ.dist p z = 4)
    (hθy : θ • y = y) (hθz : θ • z = z) :
    ∃ x a : V, Γ.dist p M = 3 ∧ Γ.Adj M x ∧ Γ.dist p x = 2 ∧ θ • x = x ∧
      (∀ L, Γ.Adj x L → θ • L = L) ∧
      a ∈ traceSet Γ p z ∧ a ≠ x ∧ θ • a = a ∧ Γ.dist a x = 4 ∧
        Γ.dist a y = 4 ∧ (∀ L, Γ.Adj a L → θ • L = L) := by
  classical
  have hpN : ∀ L, Γ.Adj p L → θ • L = L := by
    have hmem : θ ∈ fixingSubgroup H (Γ.neighborSet p) := by simpa using hθ
    exact fun L hL => (mem_fixingSubgroup_iff H).mp hmem L hL
  have hyN : ∀ L, Γ.Adj y L → θ • L = L :=
    all_lines_fixed_of_fix_of_opposite hP hpN hθy hy
  have hzN : ∀ L, Γ.Adj z L → θ • L = L :=
    all_lines_fixed_of_fix_of_opposite hP hpN hθz hzp
  have htr_y : ∀ a, a ∈ traceSet Γ p y → θ • a = a :=
    fun a ha => smul_eq_of_mem_traceSet hP hpN hyN hy ha
  have htr_z : ∀ a, a ∈ traceSet Γ p z → θ • a = a :=
    fun a ha => smul_eq_of_mem_traceSet hP hpN hzN hzp ha
  have hyz2 : Γ.dist y z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hyM hzM hzy.symm
  have hMfix : θ • M = M := line_fixed_of_fix_of_fix hP hθy hθz hyM hzM hzy
  have hdistPM : Γ.dist p M = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP (by rw [SimpleGraph.dist_comm]; exact hzp)
      hzM.symm
  let x : V := proj hP hdistPM
  have hxM : Γ.Adj M x := proj_adj hP hdistPM
  have hpx : Γ.dist p x = 2 := proj_dist hP hdistPM
  have hxz_ne : x ≠ z := by
    intro h
    rw [h] at hpx
    omega
  have hxy_ne : x ≠ y := by
    intro h
    rw [h] at hpx
    omega
  have hxz : Γ.dist x z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hxM.symm hzM hxz_ne
  have hxy : Γ.dist x y = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hxM.symm hyM.symm hxy_ne
  have hx_mem_z : x ∈ traceSet Γ p z :=
    ⟨hpx, by rw [SimpleGraph.dist_comm]; exact hxz⟩
  have hx_mem_y : x ∈ traceSet Γ p y :=
    ⟨hpx, by rw [SimpleGraph.dist_comm]; exact hxy⟩
  have hxfix : θ • x = x := by
    let Nx : V := commonNeighbor hP hpx
    have hpNx : Γ.Adj p Nx := commonNeighbor_adj_left hP hpx
    have hxNx : Γ.Adj x Nx := commonNeighbor_adj_right hP hpx
    have hNxfix : θ • Nx = Nx := hpN Nx hpNx
    have hNxM : Nx ≠ M := by
      intro h
      have hpM : Γ.Adj p M := h ▸ hpNx
      have h1 : Γ.dist p M = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hpM
      omega
    have hdistNxM : Γ.dist Nx M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hxNx.symm hxM.symm hNxM
    have hθxNx : Γ.Adj Nx (θ • x) := by
      have h := (GraphAction.adj_smul θ x Nx).mpr hxNx
      rw [hNxfix] at h
      exact h.symm
    have hθxM : Γ.Adj M (θ • x) := by
      have h := (GraphAction.adj_smul θ M x).mpr hxM
      rwa [hMfix] at h
    exact (existsUnique_commonNeighbor hP hdistNxM).unique ⟨hθxNx, hθxM⟩
      ⟨hxNx.symm, hxM⟩
  have ht2 : 2 ≤ t := by
    have h := hT p
    rw [hdeg p, if_pos hp] at h
    omega
  have hcard : 1 < (traceSet Γ p z).ncard := by
    rw [ncard_trace hP hzp, hdeg p, if_pos hp]
    omega
  obtain ⟨a, ha_mem, hax⟩ := Set.exists_ne_of_one_lt_ncard hcard x
  have ha_fix : θ • a = a := htr_z a ha_mem
  have hax4 : Γ.dist a x = 4 :=
    dist_eq_four_of_mem_trace hP hzp ha_mem hx_mem_z hax
  have hcy : c y = 0 := by
    have h : c y = c p :=
      (hP.eq_iff_even_dist c y p).2 (by rw [SimpleGraph.dist_comm, hy]; exact ⟨2, rfl⟩)
    rw [h, hp]
  have hay : Γ.dist a y = 4 := by
    have hca : c a = c p :=
      (hP.eq_iff_even_dist c a p).2 (by rw [SimpleGraph.dist_comm, ha_mem.1]; exact ⟨1, rfl⟩)
    have heven : Even (Γ.dist a y) :=
      (hP.eq_iff_even_dist c a y).1 (by rw [hca, hp, hcy])
    have hle : Γ.dist a y ≤ 4 := hP.dist_le (by norm_num) a y
    have hne0 : Γ.dist a y ≠ 0 := by
      intro h0
      have hay' : a = y := (hP.connected.dist_eq_zero_iff).mp h0
      have h2 : Γ.dist p y = 2 := by rw [← hay']; exact ha_mem.1
      omega
    have hne2 : Γ.dist a y ≠ 2 := by
      intro hay2
      obtain ⟨m, hm, -⟩ :=
        existsUnique_commonNeighbor_of_pairwise_dist_two hP hay2
          (by rw [SimpleGraph.dist_comm]; exact ha_mem.2) hyz2
      have hmM : m = M :=
        (existsUnique_commonNeighbor hP hyz2).unique ⟨hm.2.1, hm.2.2⟩
          ⟨hyM, hzM.symm⟩
      rw [hmM] at hm
      have haM : Γ.Adj M a := hm.1.symm
      have hax_eq : a = x :=
        (eq_proj hP hdistPM haM ha_mem.1).trans
          (eq_proj hP hdistPM hxM hpx).symm
      exact hax hax_eq
    obtain ⟨k, hk⟩ := heven
    omega
  have haN : ∀ L, Γ.Adj a L → θ • L = L :=
    all_lines_fixed_of_fix_of_opposite hP hyN ha_fix
      (by rw [SimpleGraph.dist_comm]; exact hay)
  have hxN : ∀ L, Γ.Adj x L → θ • L = L :=
    all_lines_fixed_of_fix_of_opposite hP haN hxfix hax4
  exact ⟨x, a, hdistPM, hxM, hpx, hxfix, hxN, ha_mem, hax, ha_fix, hax4, hay, haN⟩


theorem all_lines_fixed_of_fix_point (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {p y z M : V} (hp : c p = 0) {θ : H}
    (hθ : θ ∈ whorlGroup H Γ p) (hy : Γ.dist p y = 4)
    (hyM : Γ.Adj y M) (hzM : Γ.Adj M z) (hzy : z ≠ y) (hzp : Γ.dist p z = 4)
    (hθy : θ • y = y) (hθz : θ • z = z) {w : V} (hw : c w = 0) (hθw : θ • w = w) :
    ∀ L, Γ.Adj w L → θ • L = L := by
  classical
  have hpN : ∀ L, Γ.Adj p L → θ • L = L := by
    have hmem : θ ∈ fixingSubgroup H (Γ.neighborSet p) := by simpa using hθ
    exact fun L hL => (mem_fixingSubgroup_iff H).mp hmem L hL
  have hyN : ∀ L, Γ.Adj y L → θ • L = L :=
    all_lines_fixed_of_fix_of_opposite hP hpN hθy hy
  have hzN : ∀ L, Γ.Adj z L → θ • L = L :=
    all_lines_fixed_of_fix_of_opposite hP hpN hθz hzp
  obtain ⟨x, a, hdistPM, hxM, hpx, hxfix, hxN, ha_mem, hax, ha_fix, hax4, hay, haN⟩ :=
    whorl_projection_data hP hT c hdeg hp hθ hy hyM hzM hzy hzp hθy hθz
  have hyz2 : Γ.dist y z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hyM hzM hzy.symm
  have hpw_even : Even (Γ.dist p w) :=
    (hP.eq_iff_even_dist c p w).1 (by rw [hp, hw])
  have hpw_le : Γ.dist p w ≤ 4 := hP.dist_le (by norm_num) p w
  have hcy : c y = 0 := by
    have h : c y = c p :=
      (hP.eq_iff_even_dist c y p).2 (by rw [SimpleGraph.dist_comm, hy]; exact ⟨2, rfl⟩)
    rw [h, hp]
  have hcz : c z = 0 := by
    have h : c z = c p :=
      (hP.eq_iff_even_dist c z p).2 (by rw [SimpleGraph.dist_comm, hzp]; exact ⟨2, rfl⟩)
    rw [h, hp]
  obtain ⟨k, hk⟩ := hpw_even
  have hcases : Γ.dist p w = 0 ∨ Γ.dist p w = 2 ∨ Γ.dist p w = 4 := by omega
  intro L hwL
  rcases hcases with h0 | h2 | h4
  · have hwp : w = p := ((hP.connected.dist_eq_zero_iff).mp h0).symm
    rw [hwp] at hwL
    exact hpN L hwL
  · by_cases hwy : w ∈ traceSet Γ p y
    · by_cases hwz : w ∈ traceSet Γ p z
      · have hw_eq_x : w = x := by
          obtain ⟨m, hm, -⟩ :=
            existsUnique_commonNeighbor_of_pairwise_dist_two hP
              (by rw [SimpleGraph.dist_comm]; exact hwy.2)
              (by rw [SimpleGraph.dist_comm]; exact hwz.2) hyz2
          have hmM : m = M :=
            (existsUnique_commonNeighbor hP hyz2).unique ⟨hm.2.1, hm.2.2⟩
              ⟨hyM, hzM.symm⟩
          rw [hmM] at hm
          have hwM : Γ.Adj M w := hm.1.symm
          have h2' : Γ.dist p w = 2 := h2
          exact (eq_proj hP hdistPM hwM h2').trans (eq_proj hP hdistPM hxM hpx).symm
        rw [hw_eq_x] at hwL
        exact hxN L hwL
      · have hwz4 : Γ.dist w z = 4 := by
          have heven : Even (Γ.dist w z) :=
            (hP.eq_iff_even_dist c w z).1 (by rw [hw, hcz])
          have hle : Γ.dist w z ≤ 4 := hP.dist_le (by norm_num) w z
          have hne0 : Γ.dist w z ≠ 0 := by
            intro h0
            have hwz' : w = z := (hP.connected.dist_eq_zero_iff).mp h0
            have h2' : Γ.dist p z = 2 := by rw [← hwz']; exact h2
            omega
          have hne2 : Γ.dist w z ≠ 2 := by
            intro h2z
            exact hwz ⟨h2, by rw [SimpleGraph.dist_comm]; exact h2z⟩
          obtain ⟨j, hj⟩ := heven
          omega
        exact all_lines_fixed_of_fix_of_opposite hP hzN hθw
          (by rw [SimpleGraph.dist_comm]; exact hwz4) L hwL
    · have hwy4 : Γ.dist w y = 4 := by
        have heven : Even (Γ.dist w y) :=
          (hP.eq_iff_even_dist c w y).1 (by rw [hw, hcy])
        have hle : Γ.dist w y ≤ 4 := hP.dist_le (by norm_num) w y
        have hne0 : Γ.dist w y ≠ 0 := by
          intro h0
          have hwy' : w = y := (hP.connected.dist_eq_zero_iff).mp h0
          have h2' : Γ.dist p y = 2 := by rw [← hwy']; exact h2
          omega
        have hne2 : Γ.dist w y ≠ 2 := by
          intro h2y
          exact hwy ⟨h2, by rw [SimpleGraph.dist_comm]; exact h2y⟩
        obtain ⟨j, hj⟩ := heven
        omega
      exact all_lines_fixed_of_fix_of_opposite hP hyN hθw
        (by rw [SimpleGraph.dist_comm]; exact hwy4) L hwL
  · exact all_lines_fixed_of_fix_of_opposite hP hpN hθw h4 L hwL


end Closure

section Count

variable {Γ : SimpleGraph V} {H : Type v} [Group H] [MulAction H V] [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

theorem ncard_fixed_neighborSet_eq_of_dist_eq_four (hP : IsGeneralizedPolygon Γ 4)
    {θ : H} {L M : V} (hLM : Γ.dist L M = 4) (hLfix : θ • L = L)
    (hMfix : θ • M = M) :
    (Γ.neighborSet L ∩ {v | θ • v = v}).ncard =
      (Γ.neighborSet M ∩ {v | θ • v = v}).ncard := by
  classical
  let s : Set V := Γ.neighborSet L ∩ {v | θ • v = v}
  let t : Set V := Γ.neighborSet M ∩ {v | θ • v = v}
  have hdist : ∀ a ∈ s, Γ.dist a M = 3 := by
    intro a ha
    have haL : Γ.Adj L a := by
      simpa only [s, Set.mem_inter_iff, Set.mem_setOf_eq, mem_neighborSet] using ha |>.1
    have h := dist_eq_three_of_adj_of_dist_eq_four hP hLM haL
    rw [SimpleGraph.dist_comm]
    exact h
  have hdist' : ∀ b ∈ t, Γ.dist b L = 3 := by
    intro b hb
    have hbM : Γ.Adj M b := by
      simpa only [t, Set.mem_inter_iff, Set.mem_setOf_eq, mem_neighborSet] using hb |>.1
    have h := dist_eq_three_of_adj_of_dist_eq_four hP
      (by rw [SimpleGraph.dist_comm]; exact hLM) hbM
    rw [SimpleGraph.dist_comm]
    exact h
  refine Set.ncard_congr (fun a ha => proj hP (hdist a ha)) ?_ ?_ ?_
  · rintro a ha
    have hafix : θ • a = a := by
      simpa only [s, Set.mem_inter_iff, Set.mem_setOf_eq] using ha |>.2
    have hpadj : Γ.Adj M (proj hP (hdist a ha)) := proj_adj hP (hdist a ha)
    have hpdist : Γ.dist a (proj hP (hdist a ha)) = 2 := proj_dist hP (hdist a ha)
    have hθadj : Γ.Adj M (θ • proj hP (hdist a ha)) := by
      have h := (GraphAction.adj_smul θ (proj hP (hdist a ha)) M).mpr hpadj.symm
      rw [hMfix] at h
      exact h.symm
    have hθdist : Γ.dist a (θ • proj hP (hdist a ha)) = 2 := by
      have h := GPath.dist_smul hP.connected θ a (proj hP (hdist a ha))
      rw [hafix] at h
      exact h.trans hpdist
    exact ⟨by simpa only [t, Set.mem_inter_iff, mem_neighborSet] using hpadj,
      eq_proj hP (hdist a ha) hθadj hθdist⟩
  · intro a b ha hb heq
    have hafix : θ • a = a := by
      simpa only [s, Set.mem_inter_iff, Set.mem_setOf_eq] using ha |>.2
    have hbL : Γ.Adj L b := by
      simpa only [s, Set.mem_inter_iff, Set.mem_setOf_eq, mem_neighborSet] using hb |>.1
    have haL : Γ.Adj L a := by
      simpa only [s, Set.mem_inter_iff, Set.mem_setOf_eq, mem_neighborSet] using ha |>.1
    have hqM : Γ.Adj M (proj hP (hdist a ha)) := proj_adj hP (hdist a ha)
    have hqL : Γ.dist (proj hP (hdist a ha)) L = 3 := by
      have h := dist_eq_three_of_adj_of_dist_eq_four hP
        (by rw [SimpleGraph.dist_comm]; exact hLM) hqM
      rw [SimpleGraph.dist_comm]
      exact h
    have haq : Γ.dist a (proj hP (hdist a ha)) = 2 := proj_dist hP (hdist a ha)
    have hbq : Γ.dist b (proj hP (hdist a ha)) = 2 := by
      rw [heq]
      exact proj_dist hP (hdist b hb)
    calc a = proj hP hqL :=
          eq_proj hP hqL haL (by rw [SimpleGraph.dist_comm]; exact haq)
      _ = b := (eq_proj hP hqL hbL (by rw [SimpleGraph.dist_comm]; exact hbq)).symm
  · intro b hb
    have hbM : Γ.Adj M b := by
      simpa only [t, Set.mem_inter_iff, Set.mem_setOf_eq, mem_neighborSet] using hb |>.1
    have hbfix : θ • b = b := by
      simpa only [t, Set.mem_inter_iff, Set.mem_setOf_eq] using hb |>.2
    have hbL : Γ.dist b L = 3 := hdist' b hb
    let a : V := proj hP hbL
    have haL : Γ.Adj L a := proj_adj hP hbL
    have hba : Γ.dist b a = 2 := proj_dist hP hbL
    have hafix : θ • a = a := by
      have hθadj : Γ.Adj L (θ • a) := by
        have h := (GraphAction.adj_smul θ a L).mpr haL.symm
        rw [hLfix] at h
        exact h.symm
      have hθdist : Γ.dist b (θ • a) = 2 := by
        have h := GPath.dist_smul hP.connected θ b a
        rw [hbfix] at h
        exact h.trans hba
      exact eq_proj hP hbL hθadj hθdist
    refine ⟨a, ?_, ?_⟩
    · exact ⟨by simpa only [s, mem_neighborSet] using haL, hafix⟩
    · have hdist_a : Γ.dist a M = 3 := hdist a ⟨by simpa only [s, mem_neighborSet]
        using haL, hafix⟩
      exact (eq_proj hP hdist_a hbM (by rw [SimpleGraph.dist_comm]; exact hba)).symm

theorem ncard_fixed_neighborSet_eq_of_adj (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {θ : H} {u L M w : V}
    (hLu : Γ.Adj u L) (hMu : Γ.Adj u M)
    (hLfix : θ • L = L) (hMfix : θ • M = M)
    (huw : Γ.dist u w = 4) (hwN : ∀ N, Γ.Adj w N → θ • N = N) :
    (Γ.neighborSet L ∩ {v | θ • v = v}).ncard =
      (Γ.neighborSet M ∩ {v | θ • v = v}).ncard := by
  classical
  have hwu : Γ.dist w u = 4 := by rw [SimpleGraph.dist_comm]; exact huw
  have hwL : Γ.dist w L = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP huw hLu
  have hwM : Γ.dist w M = 3 :=
    dist_eq_three_of_adj_of_dist_eq_four hP huw hMu
  let qL : V := proj hP hwL
  have hqL : Γ.Adj L qL := proj_adj hP hwL
  have hwqL : Γ.dist w qL = 2 := proj_dist hP hwL
  let qM : V := proj hP hwM
  have hqM : Γ.Adj M qM := proj_adj hP hwM
  have hwqM : Γ.dist w qM = 2 := proj_dist hP hwM
  let badL : V := commonNeighbor hP hwqL
  let badM : V := commonNeighbor hP hwqM
  have hwbadL : Γ.Adj w badL := commonNeighbor_adj_left hP hwqL
  have hqLbadL : Γ.Adj qL badL := commonNeighbor_adj_right hP hwqL
  have hwbadM : Γ.Adj w badM := commonNeighbor_adj_left hP hwqM
  have hex : ∃ N', Γ.Adj w N' ∧ N' ≠ badL ∧ N' ≠ badM := by
    have h3 : 3 ≤ (Γ.neighborFinset w).card := by
      rw [card_neighborFinset_eq_degree]
      exact hT w
    have hpos : 0 < (((Γ.neighborFinset w).erase badL).erase badM).card := by
      have h1 := Finset.pred_card_le_card_erase (s := Γ.neighborFinset w) (a := badL)
      have h2 := Finset.pred_card_le_card_erase
        (s := (Γ.neighborFinset w).erase badL) (a := badM)
      omega
    obtain ⟨N', hN'⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_erase, mem_neighborFinset] at hN'
    exact ⟨N', hN'.2.2, hN'.2.1, hN'.1⟩
  obtain ⟨N', hwN', hN'L, hN'M⟩ := hex
  have hN'fix : θ • N' = N' := hwN N' hwN'
  have hcwu : c w = c u :=
    (hP.eq_iff_even_dist c w u).2 (by rw [hwu]; exact ⟨2, rfl⟩)
  have hcEq : c N' = c L := by
    have h1 : c N' ≠ c w := c.valid hwN'.symm
    have h2 : c L ≠ c w := by rw [hcwu]; exact (c.valid hLu).symm
    exact (by decide : ∀ a b z : Fin 2, a ≠ z → b ≠ z → a = b) _ _ _ h1 h2
  have hN'neL : N' ≠ L := by
    intro h
    rw [h] at hwN'
    have h1 : Γ.dist w L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwN'
    omega
  have hnotmeet : Γ.dist N' L ≠ 2 := by
    intro h2
    obtain ⟨x, hx, -⟩ := existsUnique_commonNeighbor hP h2
    have hwne : w ≠ x := by
      intro h
      rw [← h] at hx
      have h1 : Γ.dist w L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hx.2.symm
      omega
    have hwx : Γ.dist w x = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hwN' hx.1 hwne
    have hxqL : x = qL := eq_proj hP hwL hx.2 hwx
    have hN'common : Γ.Adj w N' ∧ Γ.Adj qL N' :=
      ⟨hwN', by rw [← hxqL]; exact hx.1.symm⟩
    have hbadLcommon : Γ.Adj w badL ∧ Γ.Adj qL badL := ⟨hwbadL, hqLbadL⟩
    have hN'bad : N' = badL :=
      (existsUnique_commonNeighbor hP hwqL).unique hN'common hbadLcommon
    exact hN'L hN'bad
  have hne0 : Γ.dist N' L ≠ 0 := by
    intro h
    exact hN'neL ((hP.connected.dist_eq_zero_iff).mp h)
  have hle : Γ.dist N' L ≤ 4 := hP.dist_le (by norm_num) N' L
  have heven : Even (Γ.dist N' L) := (hP.eq_iff_even_dist c N' L).1 hcEq
  have h4L : Γ.dist N' L = 4 := by
    obtain ⟨j, hj⟩ := heven
    omega
  have hcEqM : c N' = c M := by
    have h1 : c N' ≠ c w := c.valid hwN'.symm
    have h2 : c M ≠ c w := by rw [hcwu]; exact (c.valid hMu).symm
    exact (by decide : ∀ a b z : Fin 2, a ≠ z → b ≠ z → a = b) _ _ _ h1 h2
  have hMne : N' ≠ M := by
    intro h
    rw [h] at hwN'
    have h1 : Γ.dist w M = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwN'
    omega
  have hnotmeetM : Γ.dist N' M ≠ 2 := by
    intro h2
    obtain ⟨x, hx, -⟩ := existsUnique_commonNeighbor hP h2
    have hwne : w ≠ x := by
      intro h
      rw [← h] at hx
      have h1 : Γ.dist w M = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hx.2.symm
      omega
    have hwx : Γ.dist w x = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hwN' hx.1 hwne
    have hxqM : x = qM := eq_proj hP hwM hx.2 hwx
    have hN'common : Γ.Adj w N' ∧ Γ.Adj qM N' :=
      ⟨hwN', by rw [← hxqM]; exact hx.1.symm⟩
    have hbadMcommon : Γ.Adj w badM ∧ Γ.Adj qM badM := ⟨hwbadM, commonNeighbor_adj_right hP hwqM⟩
    have hN'bad : N' = badM :=
      (existsUnique_commonNeighbor hP hwqM).unique hN'common hbadMcommon
    exact hN'M hN'bad
  have hne0M : Γ.dist N' M ≠ 0 := by
    intro h
    exact hMne ((hP.connected.dist_eq_zero_iff).mp h)
  have hleM : Γ.dist N' M ≤ 4 := hP.dist_le (by norm_num) N' M
  have hevenM : Even (Γ.dist N' M) := (hP.eq_iff_even_dist c N' M).1 hcEqM
  have h4M : Γ.dist N' M = 4 := by
    obtain ⟨j, hj⟩ := hevenM
    omega
  exact (ncard_fixed_neighborSet_eq_of_dist_eq_four hP h4L hN'fix hLfix).symm.trans
    (ncard_fixed_neighborSet_eq_of_dist_eq_four hP h4M hN'fix hMfix)

theorem ncard_fixed_neighborSet_eq_of_whorl (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {p y z M : V} (hp : c p = 0) {θ : H}
    (hθ : θ ∈ whorlGroup H Γ p) (hy : Γ.dist p y = 4)
    (hyM : Γ.Adj y M) (hzM : Γ.Adj M z) (hzy : z ≠ y) (hzp : Γ.dist p z = 4)
    (hθy : θ • y = y) (hθz : θ • z = z) {L : V} (hcL : c L = 1)
    (hLfix : θ • L = L) :
    (Γ.neighborSet L ∩ {v | θ • v = v}).ncard =
      (Γ.neighborSet M ∩ {v | θ • v = v}).ncard := by
  classical
  have hpN : ∀ N, Γ.Adj p N → θ • N = N := by
    have hmem : θ ∈ fixingSubgroup H (Γ.neighborSet p) := by simpa using hθ
    exact fun N hN => (mem_fixingSubgroup_iff H).mp hmem N hN
  have hyN : ∀ N, Γ.Adj y N → θ • N = N :=
    all_lines_fixed_of_fix_of_opposite hP hpN hθy hy
  have hzN : ∀ N, Γ.Adj z N → θ • N = N :=
    all_lines_fixed_of_fix_of_opposite hP hpN hθz hzp
  have hyz2 : Γ.dist y z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hyM hzM hzy.symm
  have hMfix : θ • M = M := line_fixed_of_fix_of_fix hP hθy hθz hyM hzM hzy
  obtain ⟨x, a, hdistPM, hxM, hpx, hxfix, hxN, ha_mem, hax, ha_fix, hax4, hay, haN⟩ :=
    whorl_projection_data hP hT c hdeg hp hθ hy hyM hzM hzy hzp hθy hθz
  let Nx : V := commonNeighbor hP hpx
  have hpNx : Γ.Adj p Nx := commonNeighbor_adj_left hP hpx
  have hxNx : Γ.Adj x Nx := commonNeighbor_adj_right hP hpx
  have hNxfix : θ • Nx = Nx := hpN Nx hpNx
  have hcz : c z = 0 := by
    have h : c z = c p :=
      (hP.eq_iff_even_dist c z p).2 (by rw [SimpleGraph.dist_comm, hzp]; exact ⟨2, rfl⟩)
    rw [h, hp]
  have hcM : c M = 1 :=
    (by decide : ∀ u v : Fin 2, u ≠ v → v = 0 → u = 1) _ _ (c.valid hzM) hcz
  have hthroughp : ∀ N, Γ.Adj p N → θ • N = N →
      (Γ.neighborSet N ∩ {v | θ • v = v}).ncard =
        (Γ.neighborSet M ∩ {v | θ • v = v}).ncard := by
    intro N hNp hNfix
    by_cases hNxe : N = Nx
    · rw [hNxe]
      have hNxfix' : θ • Nx = Nx := by rwa [hNxe] at hNfix
      exact ncard_fixed_neighborSet_eq_of_adj hP hT c (u := x) (L := Nx) (M := M) (w := a)
        hxNx hxM.symm hNxfix' hMfix (by rw [SimpleGraph.dist_comm]; exact hax4) haN
    · have hNMne : N ≠ M := by
        intro h
        rw [h] at hNp
        have h1 : Γ.dist p M = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hNp
        omega
      have hcN : c N = 1 :=
        (by decide : ∀ u v : Fin 2, u ≠ v → v = 0 → u = 1) (c N) (c p)
          (c.valid hNp).symm hp
      have hcEq : c N = c M := by rw [hcN, hcM]
      have hnotmeet : Γ.dist N M ≠ 2 := by
        intro h2
        obtain ⟨v, hv, -⟩ := existsUnique_commonNeighbor hP h2
        have hpv_ne : p ≠ v := by
          intro h
          rw [← h] at hv
          have h1 : Γ.dist p M = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hv.2.symm
          omega
        have hpv : Γ.dist p v = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP hNp hv.1 hpv_ne
        have hvx : v = x :=
          (eq_proj hP hdistPM hv.2 hpv).trans (eq_proj hP hdistPM hxM hpx).symm
        have hNcommon : Γ.Adj p N ∧ Γ.Adj x N :=
          ⟨hNp, by rw [← hvx]; exact hv.1.symm⟩
        have hNxcommon : Γ.Adj p Nx ∧ Γ.Adj x Nx :=
          ⟨hpNx, hxNx⟩
        exact hNxe ((existsUnique_commonNeighbor hP hpx).unique hNcommon hNxcommon)
      have hne0 : Γ.dist N M ≠ 0 := by
        intro h
        exact hNMne ((hP.connected.dist_eq_zero_iff).mp h)
      have hle : Γ.dist N M ≤ 4 := hP.dist_le (by norm_num) N M
      have heven : Even (Γ.dist N M) := (hP.eq_iff_even_dist c N M).1 hcEq
      have h4 : Γ.dist N M = 4 := by
        obtain ⟨j, hj⟩ := heven
        omega
      exact ncard_fixed_neighborSet_eq_of_dist_eq_four hP h4 hNfix hMfix
  by_cases hLp : Γ.Adj p L
  · exact hthroughp L hLp hLfix
  · have hcne : c p ≠ c L := by rw [hp, hcL]; decide
    have hodd : Odd (Γ.dist p L) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      exact hcne ((hP.eq_iff_even_dist c p L).2 heven)
    have hle : Γ.dist p L ≤ 4 := hP.dist_le (by norm_num) p L
    have hne1 : Γ.dist p L ≠ 1 := fun h =>
      hLp (SimpleGraph.dist_eq_one_iff_adj.mp h)
    have hdistpL : Γ.dist p L = 3 := by
      obtain ⟨j, hj⟩ := hodd
      omega
    let q : V := proj hP hdistpL
    have hqL : Γ.Adj L q := proj_adj hP hdistpL
    have hpq : Γ.dist p q = 2 := proj_dist hP hdistpL
    let Nq : V := commonNeighbor hP hpq
    have hpNq : Γ.Adj p Nq := commonNeighbor_adj_left hP hpq
    have hqNq : Γ.Adj q Nq := commonNeighbor_adj_right hP hpq
    have hNqfix : θ • Nq = Nq := hpN Nq hpNq
    have hLNq : L ≠ Nq := by
      intro h
      exact hLp (h ▸ hpNq)
    have hdistLNq : Γ.dist L Nq = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hqL hqNq hLNq
    have hcq : c q = 0 := by
      have h : c q = c p :=
        (hP.eq_iff_even_dist c q p).2 (by rw [SimpleGraph.dist_comm, hpq]; exact ⟨1, rfl⟩)
      rw [h, hp]
    have hcy : c y = 0 := by
      have h : c y = c p :=
        (hP.eq_iff_even_dist c y p).2 (by rw [SimpleGraph.dist_comm, hy]; exact ⟨2, rfl⟩)
      rw [h, hp]
    have hcx : c x = 0 := by
      have h : c x = c p :=
        (hP.eq_iff_even_dist c x p).2 (by rw [SimpleGraph.dist_comm, hpx]; exact ⟨1, rfl⟩)
      rw [h, hp]
    have hw_exists : ∃ w : V, Γ.dist q w = 4 ∧ ∀ N, Γ.Adj w N → θ • N = N := by
      by_cases hqy : q ∈ traceSet Γ p y
      · by_cases hqz : q ∈ traceSet Γ p z
        · have hqx : q = x := by
            obtain ⟨m, hm, -⟩ :=
              existsUnique_commonNeighbor_of_pairwise_dist_two hP
                (by rw [SimpleGraph.dist_comm]; exact hqy.2)
                (by rw [SimpleGraph.dist_comm]; exact hqz.2) hyz2
            have hmM : m = M :=
              (existsUnique_commonNeighbor hP hyz2).unique ⟨hm.2.1, hm.2.2⟩
                ⟨hyM, hzM.symm⟩
            rw [hmM] at hm
            have hqM : Γ.Adj M q := hm.1.symm
            exact (eq_proj hP hdistPM hqM hpq).trans
              (eq_proj hP hdistPM hxM hpx).symm
          exact ⟨a, by rw [hqx, SimpleGraph.dist_comm]; exact hax4, haN⟩
        · have hqz4 : Γ.dist q z = 4 := by
            have heven : Even (Γ.dist q z) :=
              (hP.eq_iff_even_dist c q z).1 (by rw [hcq, hcz])
            have hle : Γ.dist q z ≤ 4 := hP.dist_le (by norm_num) q z
            have hne0 : Γ.dist q z ≠ 0 := by
              intro h0
              have hqz' : q = z := (hP.connected.dist_eq_zero_iff).mp h0
              have h2 : Γ.dist p z = 2 := by rw [← hqz']; exact hpq
              omega
            have hne2 : Γ.dist q z ≠ 2 := by
              intro h2
              exact hqz ⟨hpq, by rw [SimpleGraph.dist_comm]; exact h2⟩
            obtain ⟨j, hj⟩ := heven
            omega
          exact ⟨z, hqz4, hzN⟩
      · have hqy4 : Γ.dist q y = 4 := by
          have heven : Even (Γ.dist q y) :=
            (hP.eq_iff_even_dist c q y).1 (by rw [hcq, hcy])
          have hle : Γ.dist q y ≤ 4 := hP.dist_le (by norm_num) q y
          have hne0 : Γ.dist q y ≠ 0 := by
            intro h0
            have hqy' : q = y := (hP.connected.dist_eq_zero_iff).mp h0
            have h2 : Γ.dist p y = 2 := by rw [← hqy']; exact hpq
            omega
          have hne2 : Γ.dist q y ≠ 2 := by
            intro h2
            exact hqy ⟨hpq, by rw [SimpleGraph.dist_comm]; exact h2⟩
          obtain ⟨j, hj⟩ := heven
          omega
        exact ⟨y, hqy4, hyN⟩
    obtain ⟨w, hqw, hwN⟩ := hw_exists
    exact (ncard_fixed_neighborSet_eq_of_adj hP hT c hqL.symm hqNq hLfix hNqfix hqw hwN).trans
      (hthroughp Nq hpNq hNqfix)

end Count

end CFSG.Geometry.GeneralizedQuadrangles

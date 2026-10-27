module

public import CFSG.Geometry.GeneralizedQuadrangles.Whorls2
public import CFSG.Geometry.GeneralizedQuadrangles.Counting.Substructure

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin

universe u v

variable {V : Type u} {Γ : SimpleGraph V} {H : Type v} [Group H] [MulAction H V]
  [FaithfulSMul H V] [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

theorem eq_one_of_mem_whorlGroup_of_fix (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hst : s ≤ t) {p y z M : V}
    (hp : c p = 0) {θ : H} (hθ : θ ∈ whorlGroup H Γ p) (hy : Γ.dist p y = 4)
    (hyM : Γ.Adj y M) (hzM : Γ.Adj M z) (hzy : z ≠ y) (hzp : Γ.dist p z = 4)
    (hθy : θ • y = y) (hθz : θ • z = z) : θ = 1 := by
  classical
  have hpN : ∀ L, Γ.Adj p L → θ • L = L := by
    have hmem : θ ∈ fixingSubgroup H (Γ.neighborSet p) := by simpa using hθ
    exact fun L hL => (mem_fixingSubgroup_iff H).mp hmem L hL
  have hMfix : θ • M = M := line_fixed_of_fix_of_fix hP hθy hθz hyM hzM hzy
  obtain ⟨x, a, hdistPM, hxM, hpx, hxfix, hxN, ha_mem, hax, ha_fix, hax4, hay, haN⟩ :=
    whorl_projection_data hP hT c hdeg hp hθ hy hyM hzM hzy hzp hθy hθz
  have hxy_ne : x ≠ y := by
    intro h
    rw [h] at hpx
    omega
  have hxz_ne : x ≠ z := by
    intro h
    rw [h] at hpx
    omega
  have hpfix : θ • p = p := by
    have h2lt : 1 < (Γ.neighborFinset p).card := by
      rw [card_neighborFinset_eq_degree, hdeg p, if_pos hp]
      have h := hT p
      rw [hdeg p, if_pos hp] at h
      omega
    obtain ⟨L1, hL1, L2, hL2, hL12⟩ := Finset.one_lt_card.mp h2lt
    have hL1' : Γ.Adj p L1 := by simpa using hL1
    have hL2' : Γ.Adj p L2 := by simpa using hL2
    have hL1fix : θ • L1 = L1 := hpN L1 hL1'
    have hL2fix : θ • L2 = L2 := hpN L2 hL2'
    have hdist12 : Γ.dist L1 L2 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hL1'.symm hL2' hL12
    have hθ1 : Γ.Adj L1 (θ • p) := by
      have h := (GraphAction.adj_smul θ p L1).mpr hL1'
      rw [hL1fix] at h
      exact h.symm
    have hθ2 : Γ.Adj L2 (θ • p) := by
      have h := (GraphAction.adj_smul θ p L2).mpr hL2'
      rw [hL2fix] at h
      exact h.symm
    exact (existsUnique_commonNeighbor hP hdist12).unique ⟨hθ1, hθ2⟩
      ⟨hL1'.symm, hL2'.symm⟩
  have hcz : c z = 0 := by
    have h : c z = c p :=
      (hP.eq_iff_even_dist c z p).2 (by rw [SimpleGraph.dist_comm, hzp]; exact ⟨2, rfl⟩)
    rw [h, hp]
  have hcM : c M = 1 :=
    (by decide : ∀ u w : Fin 2, u ≠ w → w = 0 → u = 1) (c M) (c z) (c.valid hzM) hcz
  let f : ℕ := (Γ.neighborSet M ∩ {v | θ • v = v}).ncard
  have hf3 : 3 ≤ f := by
    have hsub : ({x, y, z} : Set V) ⊆ Γ.neighborSet M ∩ {v | θ • v = v} := by
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨hxM, hxfix⟩
      · exact ⟨hyM.symm, hθy⟩
      · exact ⟨hzM, hθz⟩
    have hle := Set.ncard_le_ncard hsub
    have h3 : ({x, y, z} : Set V).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨x, y, z, hxy_ne, hxz_ne, hzy.symm, rfl⟩
    rw [h3] at hle
    exact hle
  let F : Set V := {v | c v = 0 ∧ θ • v = v}
  let B : Set V := {v | c v = 1 ∧ θ • v = v}
  have hne : B.Nonempty := ⟨M, hcM, hMfix⟩
  have hF : ∀ v ∈ F, c v = 0 := fun v hv => hv.1
  have hB : ∀ L ∈ B, c L = 1 := fun L hL => hL.1
  have hFB : ∀ v ∈ F, ∀ L, Γ.Adj v L → L ∈ B := by
    rintro v ⟨hv0, hvfix⟩ L hvL
    exact ⟨(by decide : ∀ u w : Fin 2, u ≠ w → u = 0 → w = 1) (c v) (c L)
      (c.valid hvL) hv0,
      all_lines_fixed_of_fix_point hP hT c hdeg hp hθ hy hyM hzM hzy hzp hθy hθz hv0 hvfix
        L hvL⟩
  have hBF : ∀ L ∈ B, (Γ.neighborSet L ∩ F).ncard = (f - 1) + 1 := by
    rintro L ⟨hcL, hLfix⟩
    have hcount := ncard_fixed_neighborSet_eq_of_whorl hP hT c hdeg hp hθ hy hyM hzM hzy hzp
      hθy hθz hcL hLfix
    have hEq : Γ.neighborSet L ∩ F = Γ.neighborSet L ∩ {v | θ • v = v} := by
      ext v
      constructor
      · rintro ⟨hv, hv0, hvf⟩
        exact ⟨hv, hvf⟩
      · rintro ⟨hv, hvf⟩
        exact ⟨hv, (by decide : ∀ u w : Fin 2, u ≠ w → u = 1 → w = 0) (c L) (c v)
          (c.valid hv) hcL, hvf⟩
    rw [hEq, hcount]
    show f = (f - 1) + 1
    omega
  have hBB : ∀ L ∈ B, ∀ M' ∈ B, L ≠ M' → ∀ v, Γ.Adj L v → Γ.Adj M' v → v ∈ F := by
    rintro L ⟨hcL, hLfix⟩ M' ⟨hcM', hM'fix⟩ hne' v hvL hvM'
    have hdist : Γ.dist L M' = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hvL hvM'.symm hne'
    have hvfix : θ • v = v := by
      have hθL : Γ.Adj L (θ • v) := by
        have h := (GraphAction.adj_smul θ v L).mpr hvL.symm
        rw [hLfix] at h
        exact h.symm
      have hθM' : Γ.Adj M' (θ • v) := by
        have h := (GraphAction.adj_smul θ v M').mpr hvM'.symm
        rw [hM'fix] at h
        exact h.symm
      exact (existsUnique_commonNeighbor hP hdist).unique ⟨hθL, hθM'⟩ ⟨hvL, hvM'⟩
    exact ⟨(by decide : ∀ u w : Fin 2, u ≠ w → u = 1 → w = 0) (c L) (c v)
      (c.valid hvL) hcL, hvfix⟩
  have hres := eq_or_mul_le_of_closed hP hT c hdeg hF hB hFB hBF hBB hne
  have hs2 : 2 ≤ s := by
    obtain ⟨L0, hL0⟩ := exists_line hP hT c
    have h := hT L0
    rw [hdeg L0, if_neg (by rw [hL0]; decide)] at h
    omega
  have ht2 : 2 ≤ t := by
    have h := hT p
    rw [hdeg p, if_pos hp] at h
    omega
  have hs'_le : ¬ (f - 1) * t ≤ s := by
    have hs'2 : 2 ≤ f - 1 := by omega
    have h1 : 2 * t ≤ (f - 1) * t := Nat.mul_le_mul_right t hs'2
    have h2 : 2 * s ≤ 2 * t := Nat.mul_le_mul_left 2 hst
    omega
  have hs'eq : f - 1 = s := hres.resolve_right hs'_le
  have hfs : f = s + 1 := by omega
  have hb' : ∀ L ∈ B, (Γ.neighborSet L ∩ F).ncard = s + 1 := by
    intro L hL
    rw [hBF L hL, hs'eq]
  have hfixed_line_points : ∀ L, c L = 1 → θ • L = L →
      Γ.neighborSet L ⊆ {v | θ • v = v} := by
    intro L hcL hLfix
    have hdegL : Γ.degree L = s + 1 := by
      rw [hdeg L, if_neg (by rw [hcL]; decide)]
    have hcount : (Γ.neighborSet L ∩ {v | θ • v = v}).ncard = s + 1 := by
      have h := hb' L ⟨hcL, hLfix⟩
      have hEq : Γ.neighborSet L ∩ F = Γ.neighborSet L ∩ {v | θ • v = v} := by
        ext v
        constructor
        · rintro ⟨hv, hv0, hvf⟩
          exact ⟨hv, hvf⟩
        · rintro ⟨hv, hvf⟩
          exact ⟨hv, (by decide : ∀ u w : Fin 2, u ≠ w → u = 1 → w = 0) (c L) (c v)
            (c.valid hv) hcL, hvf⟩
      rwa [hEq] at h
    have hcard : (Γ.neighborSet L).ncard =
        (Γ.neighborSet L ∩ {v | θ • v = v}).ncard := by
      rw [SimpleGraph.ncard_neighborSet, hdegL, hcount]
    have heq : Γ.neighborSet L ∩ {v | θ • v = v} = Γ.neighborSet L :=
      Set.eq_of_subset_of_ncard_le Set.inter_subset_left (le_of_eq hcard)
    intro v hv
    have hv' : v ∈ Γ.neighborSet L ∩ {v | θ • v = v} := by rw [heq]; exact hv
    exact hv'.2
  have hperp : ∀ q, Γ.dist p q ≤ 2 → θ • q = q := by
    intro q hq
    have hcases : Γ.dist p q = 0 ∨ Γ.dist p q = 1 ∨ Γ.dist p q = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · have hqp : q = p := ((hP.connected.dist_eq_zero_iff).mp h0).symm
      rw [hqp]
      exact hpfix
    · exact hpN q (SimpleGraph.dist_eq_one_iff_adj.mp h1)
    · let N : V := commonNeighbor hP h2
      have hNp : Γ.Adj p N := commonNeighbor_adj_left hP h2
      have hNq : Γ.Adj q N := commonNeighbor_adj_right hP h2
      have hcN : c N = 1 :=
        (by decide : ∀ u w : Fin 2, u ≠ w → u = 0 → w = 1) (c p) (c N) (c.valid hNp) hp
      have hNfix : θ • N = N := hpN N hNp
      exact hfixed_line_points N hcN hNfix (hNq.symm)
  have hall_lines : ∀ L, c L = 1 → θ • L = L := by
    intro L hcL
    by_cases hLp : Γ.Adj p L
    · exact hpN L hLp
    · have hcne : c p ≠ c L := by rw [hp, hcL]; decide
      have hodd : Odd (Γ.dist p L) := by
        rw [← Nat.not_even_iff_odd]
        intro heven
        exact hcne ((hP.eq_iff_even_dist c p L).2 heven)
      have hle : Γ.dist p L ≤ 4 := hP.dist_le (by norm_num) p L
      have hne1 : Γ.dist p L ≠ 1 := fun h => hLp (SimpleGraph.dist_eq_one_iff_adj.mp h)
      have hdist : Γ.dist p L = 3 := by
        obtain ⟨j, hj⟩ := hodd
        omega
      let q : V := proj hP hdist
      have hqL : Γ.Adj L q := proj_adj hP hdist
      have hpq : Γ.dist p q = 2 := proj_dist hP hdist
      have hqfix : θ • q = q := hperp q (by omega)
      have hcq : c q = 0 := by
        have h : c q = c p :=
          (hP.eq_iff_even_dist c q p).2 (by rw [SimpleGraph.dist_comm, hpq]; exact ⟨1, rfl⟩)
        rw [h, hp]
      exact all_lines_fixed_of_fix_point hP hT c hdeg hp hθ hy hyM hzM hzy hzp hθy hθz
        hcq hqfix L hqL.symm
  refine eq_of_smul_eq_smul (m₁ := θ) (m₂ := 1) (fun v : V => ?_)
  rw [one_smul]
  have hfin : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide
  rcases hfin (c v) with hv0 | hv1
  · have h2lt : 1 < (Γ.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree, hdeg v, if_pos hv0]
      have h := hT v
      rw [hdeg v, if_pos hv0] at h
      omega
    obtain ⟨L1, hL1, L2, hL2, hL12⟩ := Finset.one_lt_card.mp h2lt
    have hL1' : Γ.Adj v L1 := by simpa using hL1
    have hL2' : Γ.Adj v L2 := by simpa using hL2
    have hc1 : c L1 = 1 :=
      (by decide : ∀ u w : Fin 2, u ≠ w → u = 0 → w = 1) (c v) (c L1) (c.valid hL1') hv0
    have hc2 : c L2 = 1 :=
      (by decide : ∀ u w : Fin 2, u ≠ w → u = 0 → w = 1) (c v) (c L2) (c.valid hL2') hv0
    have hf1 : θ • L1 = L1 := hall_lines L1 hc1
    have hf2 : θ • L2 = L2 := hall_lines L2 hc2
    have hdist12 : Γ.dist L1 L2 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hL1'.symm hL2' hL12
    have hθ1 : Γ.Adj L1 (θ • v) := by
      have h := (GraphAction.adj_smul θ v L1).mpr hL1'
      rw [hf1] at h
      exact h.symm
    have hθ2 : Γ.Adj L2 (θ • v) := by
      have h := (GraphAction.adj_smul θ v L2).mpr hL2'
      rw [hf2] at h
      exact h.symm
    exact (existsUnique_commonNeighbor hP hdist12).unique ⟨hθ1, hθ2⟩
      ⟨hL1'.symm, hL2'.symm⟩
  · exact hall_lines v hv1

theorem eq_one_of_mem_whorlGroup_of_fix_two (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hst : s ≤ t) {p : V}
    (hp : c p = 0) (hspan : ∀ x, Γ.dist p x = 4 → (spanSet Γ p x).ncard = 2) {θ : H}
    (hθ : θ ∈ whorlGroup H Γ p) {y y' : V} (hy : Γ.dist p y = 4) (hy' : Γ.dist p y' = 4)
    (hyy' : y ≠ y') (h1 : θ • y = y) (h2 : θ • y' = y') : θ = 1 := by
  classical
  by_cases hd : Γ.dist y y' = 2
  · let M : V := commonNeighbor hP hd
    exact eq_one_of_mem_whorlGroup_of_fix hP hT c hdeg hst hp hθ hy
      (commonNeighbor_adj_left hP hd) (commonNeighbor_adj_right hP hd).symm hyy'.symm hy' h1 h2
  · have hpN : ∀ L, Γ.Adj p L → θ • L = L := by
      have hmem : θ ∈ fixingSubgroup H (Γ.neighborSet p) := by simpa using hθ
      exact fun L hL => (mem_fixingSubgroup_iff H).mp hmem L hL
    have hyN : ∀ L, Γ.Adj y L → θ • L = L :=
      all_lines_fixed_of_fix_of_opposite hP hpN h1 hy
    have hspan2 : spanSet Γ p y = {p, y} := by
      have hsub : ({p, y} : Set V) ⊆ spanSet Γ p y := by
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact left_mem_spanSet hy
        · exact right_mem_spanSet hy
      have hpne : p ≠ y := by
        intro h
        rw [h] at hy
        simp at hy
      have h2p : ({p, y} : Set V).ncard = 2 :=
        Set.ncard_eq_two.mpr ⟨p, y, hpne, rfl⟩
      have hsp : (spanSet Γ p y).ncard = 2 := hspan y hy
      exact (Set.eq_of_subset_of_ncard_le hsub (by rw [h2p, hsp])).symm
    have hy'_notspan : y' ∉ spanSet Γ p y := by
      rw [hspan2]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨by rintro rfl; simp at hy', hyy'.symm⟩
    rw [mem_spanSet] at hy'_notspan
    push Not at hy'_notspan
    obtain ⟨a, ha, hgt⟩ := hy'_notspan
    have hca : c a = 0 := by
      have h : c a = c p :=
        (hP.eq_iff_even_dist c a p).2 (by
          rw [SimpleGraph.dist_comm, ha.1]; exact ⟨1, rfl⟩)
      rw [h, hp]
    have hcy' : c y' = 0 := by
      have h : c y' = c p :=
        (hP.eq_iff_even_dist c y' p).2 (by
          rw [SimpleGraph.dist_comm, hy']; exact ⟨2, rfl⟩)
      rw [h, hp]
    have heven : Even (Γ.dist a y') :=
      (hP.eq_iff_even_dist c a y').1 (by rw [hca, hcy'])
    have hle : Γ.dist a y' ≤ 4 := hP.dist_le (by norm_num) a y'
    have hay' : Γ.dist a y' = 4 := by
      have hgt' : 2 < Γ.dist a y' := by
        rw [SimpleGraph.dist_comm]
        omega
      obtain ⟨j, hj⟩ := heven
      omega
    have ha_fix : θ • a = a := smul_eq_of_mem_traceSet hP hpN hyN hy ha
    let K : V := commonNeighbor hP ha.2
    have hyK : Γ.Adj y K := commonNeighbor_adj_left hP ha.2
    have haK : Γ.Adj a K := commonNeighbor_adj_right hP ha.2
    have hKfix : θ • K = K := hyN K hyK
    have hdisty'K : Γ.dist y' K = 3 :=
      dist_eq_three_of_adj_of_dist_eq_four hP hay' haK
    let z : V := proj hP hdisty'K
    have hzK : Γ.Adj K z := proj_adj hP hdisty'K
    have hzy' : Γ.dist z y' = 2 := by
      rw [SimpleGraph.dist_comm]
      exact proj_dist hP hdisty'K
    have hzfix : θ • z = z := by
      have hθK : Γ.Adj K (θ • z) := by
        have h := (GraphAction.adj_smul θ z K).mpr hzK.symm
        rw [hKfix] at h
        exact h.symm
      have hθz' : Γ.dist y' (θ • z) = 2 := by
        have h := GPath.dist_smul hP.connected θ y' z
        rw [h2] at h
        exact h.trans (by rw [SimpleGraph.dist_comm]; exact hzy')
      exact eq_proj hP hdisty'K hθK hθz'
    have hzy : z ≠ y := by
      intro h
      rw [h] at hzy'
      exact hd hzy'
    have hdistpK : Γ.dist p K = 3 :=
      dist_eq_three_of_adj_of_dist_eq_four hP (by rw [SimpleGraph.dist_comm]; exact hy) hyK
    have hzp : Γ.dist p z = 4 := by
      have hcza : c z = c a :=
        (by decide : ∀ u w zz : Fin 2, u ≠ zz → w ≠ zz → u = w) (c z) (c a) (c K)
          (c.valid hzK).symm (c.valid haK)
      have hczp : c z = c p := by rw [hcza, hca, hp]
      have hevenz : Even (Γ.dist p z) := (hP.eq_iff_even_dist c p z).1 hczp.symm
      have hlez : Γ.dist p z ≤ 4 := hP.dist_le (by norm_num) p z
      have hne0 : Γ.dist p z ≠ 0 := by
        intro h0
        have hzp0 : z = p := ((hP.connected.dist_eq_zero_iff).mp h0).symm
        rw [hzp0] at hzy'
        omega
      have hne2 : Γ.dist p z ≠ 2 := by
        intro h2z
        have haproj : a = proj hP hdistpK :=
          eq_proj hP hdistpK haK.symm ha.1
        have hzproj : z = proj hP hdistpK := eq_proj hP hdistpK hzK h2z
        have hza : z = a := hzproj.trans haproj.symm
        rw [hza] at hzy'
        omega
      obtain ⟨j, hj⟩ := hevenz
      omega
    exact eq_one_of_mem_whorlGroup_of_fix hP hT c hdeg hst hp hθ hy hyK hzK hzy hzp h1 hzfix

end CFSG.Geometry.GeneralizedQuadrangles

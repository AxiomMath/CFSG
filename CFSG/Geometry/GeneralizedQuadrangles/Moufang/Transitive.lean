module

public import CFSG.Geometry.GeneralizedQuadrangles.Basic
public import CFSG.Quasithin.Recognition.Stroth.Weiss80AssemblyFacts

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth

open scoped Pointwise

variable {V : Type}

section Equivariance

variable {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

theorem smul_traceSet (hΓ : Γ.Connected) (g : H) (x y : V) :
    g • traceSet Γ x y = traceSet Γ (g • x) (g • y) := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hw
    exact ⟨by rw [GPath.dist_smul hΓ]; exact hu.1,
      by rw [GPath.dist_smul hΓ]; exact hu.2⟩
  · intro hw
    rw [Set.mem_smul_set]
    refine ⟨g⁻¹ • w, ⟨?_, ?_⟩, by rw [smul_inv_smul]⟩
    · calc
        Γ.dist x (g⁻¹ • w) = Γ.dist (g⁻¹ • (g • x)) (g⁻¹ • w) := by simp
        _ = Γ.dist (g • x) w := GPath.dist_smul hΓ g⁻¹ (g • x) w
        _ = 2 := hw.1
    · calc
        Γ.dist y (g⁻¹ • w) = Γ.dist (g⁻¹ • (g • y)) (g⁻¹ • w) := by simp
        _ = Γ.dist (g • y) w := GPath.dist_smul hΓ g⁻¹ (g • y) w
        _ = 2 := hw.2

theorem smul_spanSet (hΓ : Γ.Connected) (g : H) (x y : V) :
    g • spanSet Γ x y = spanSet Γ (g • x) (g • y) := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_spanSet, mem_spanSet]
  constructor
  · intro h w hw
    have hw' : g⁻¹ • w ∈ traceSet Γ x y := by
      have hmem : w ∈ g • traceSet Γ x y := by
        rw [smul_traceSet hΓ g x y]
        exact hw
      exact Set.mem_smul_set_iff_inv_smul_mem.mp hmem
    have hz := h (g⁻¹ • w) hw'
    have hdist : Γ.dist z w = Γ.dist (g⁻¹ • z) (g⁻¹ • w) := by
      have h := GPath.dist_smul hΓ g (g⁻¹ • z) (g⁻¹ • w)
      simpa using h
    rw [hdist]
    exact hz
  · intro h w hw
    have hw' : g • w ∈ traceSet Γ (g • x) (g • y) := by
      rw [← smul_traceSet hΓ g x y]
      exact Set.mem_smul_set.mpr ⟨w, hw, rfl⟩
    have hz := h (g • w) hw'
    have hdist : Γ.dist (g⁻¹ • z) w = Γ.dist z (g • w) := by
      have h := GPath.dist_smul hΓ g (g⁻¹ • z) w
      simpa using h.symm
    rw [hdist]
    exact hz

end Equivariance

section LocalTransitivity

variable {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

theorem exists_adj_ne_two (hT : IsThick Γ) (v a b : V) :
    ∃ u, Γ.Adj v u ∧ u ≠ a ∧ u ≠ b := by
  classical
  have h3 : 3 ≤ (Γ.neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree]
    exact hT v
  have hpos : 0 < (((Γ.neighborFinset v).erase a).erase b).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Γ.neighborFinset v) (a := a)
    have h2 := Finset.pred_card_le_card_erase (s := (Γ.neighborFinset v).erase a) (a := b)
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_erase, mem_neighborFinset] at hu
  exact ⟨u, hu.2.2, hu.2.1, hu.1⟩

theorem exists_smul_eq_of_adj (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    {L x x' : V} (hx : Γ.Adj L x) (hx' : Γ.Adj L x') : ∃ g : H, g • x = x' := by
  classical
  by_cases hxx : x = x'
  · exact ⟨1, by simp [hxx]⟩
  obtain ⟨y, hLy, hyx, hyx'⟩ := exists_adj_ne_two hT L x x'
  obtain ⟨M, hyM, hML, -⟩ := exists_adj_ne_two hT y L y
  obtain ⟨P, hMP, hPy, -⟩ := exists_adj_ne_two hT M y M
  obtain ⟨Q, hPQ, hQM, -⟩ := exists_adj_ne_two hT P M P
  let q1 : GPath Γ 1 := GPath.ofAdj hLy.symm
  let q2 : GPath Γ 2 := GPath.cons M q1 hyM.symm
  let q3 : GPath Γ 3 := GPath.cons P q2 hMP.symm
  let q4 : GPath Γ 4 := GPath.cons Q q3 hPQ.symm
  have hq1_0 : q1 0 = y := by simp [q1]
  have hq1_1 : q1 1 = L := by simp [q1]
  have hq2_1 : q2 1 = y := by
    rw [show q2 1 = q1 0 from by simpa using GPath.cons_succ M q1 hyM.symm 0, hq1_0]
  have hq3_1 : q3 1 = M := by
    rw [show q3 1 = q2 0 from by simpa using GPath.cons_succ P q2 hMP.symm 0]
    exact GPath.cons_zero M q1 hyM.symm
  have hq4_3 : q4 3 = y := by
    have h1 : q4 3 = q3 2 := by simpa using GPath.cons_succ Q q3 hPQ.symm 2
    have h2 : q3 2 = q2 1 := by simpa using GPath.cons_succ P q2 hMP.symm 1
    rw [h1, h2, hq2_1]
  have hq4_4 : q4 4 = L := by
    have h43 : q4 4 = q3 3 := by simpa using GPath.cons_succ Q q3 hPQ.symm 3
    have h32 : q3 3 = q2 2 := by simpa using GPath.cons_succ P q2 hMP.symm 2
    have h21 : q2 2 = q1 1 := by simpa using GPath.cons_succ M q1 hyM.symm 1
    rw [h43, h32, h21, hq1_1]
  have hq1 : q1.NoBack := by
    intro i hi
    omega
  have hq2 : q2.NoBack := by
    refine GPath.noBack_cons M q1 hyM.symm hq1 ?_
    rw [hq1_1]
    exact hML
  have hq3 : q3.NoBack := by
    refine GPath.noBack_cons P q2 hMP.symm hq2 ?_
    rw [hq2_1]
    exact hPy
  have hq4 : q4.NoBack := by
    refine GPath.noBack_cons Q q3 hPQ.symm hq3 ?_
    rw [hq3_1]
    exact hQM
  obtain ⟨g, -, hgx⟩ := hM q4 hq4 x x' (by rw [hq4_4]; exact hx)
    (by rw [hq4_4]; exact hx') (by rw [hq4_3]; exact hyx.symm)
    (by rw [hq4_3]; exact hyx'.symm)
  exact ⟨g, hgx⟩

end LocalTransitivity

section ColorTransitive

variable {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

theorem exists_smul_eq_of_color_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) (c : Γ.Coloring (Fin 2)) {x x' : V}
    (hc : c x = c x') : ∃ g : H, g • x = x' := by
  classical
  by_cases hxx : x = x'
  · exact ⟨1, by simp [hxx]⟩
  have heven : Even (Γ.dist x x') := (hP.eq_iff_even_dist c x x').1 hc
  have hle : Γ.dist x x' ≤ 4 := hP.dist_le (by norm_num) x x'
  obtain ⟨k, hk⟩ := heven
  have hk2 : k ≤ 2 := by omega
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      have hdist0 : Γ.dist x x' = 0 := by omega
      exact hxx ((hP.connected.dist_eq_zero_iff).mp hdist0)
    · exact h0
  interval_cases k
  · have h2 : Γ.dist x x' = 2 := by omega
    exact exists_smul_eq_of_adj hT hM (commonNeighbor_adj_left hP h2).symm
      (commonNeighbor_adj_right hP h2).symm
  · have h4 : Γ.dist x x' = 4 := by omega
    obtain ⟨L, hxL, -⟩ := exists_adj_ne_two hT x x x
    have hx'L : Γ.dist x' L = 3 := dist_eq_three_of_adj_of_dist_eq_four hP h4 hxL
    let w := proj hP hx'L
    have hLw : Γ.Adj L w := by simpa [w] using proj_adj hP hx'L
    have hwx' : Γ.dist x' w = 2 := by simpa [w] using proj_dist hP hx'L
    obtain ⟨g₁, hg₁⟩ := exists_smul_eq_of_adj hT hM hxL.symm hLw
    have hw'x : Γ.dist w x' = 2 := by rw [dist_comm]; exact hwx'
    let L' := commonNeighbor hP hw'x
    have hL'w : Γ.Adj L' w := by
      simpa [L'] using (commonNeighbor_adj_left hP hw'x).symm
    have hL'x' : Γ.Adj L' x' := by
      simpa [L'] using (commonNeighbor_adj_right hP hw'x).symm
    obtain ⟨g₂, hg₂⟩ := exists_smul_eq_of_adj hT hM hL'w hL'x'
    exact ⟨g₂ * g₁, by rw [mul_smul, hg₁, hg₂]⟩

end ColorTransitive

section StabilizerTransitive

variable {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V]
  [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

private theorem exists_smul_fix_of_dist_eq_four (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) {x L₀ M : V} (hxL₀ : Γ.Adj x L₀) (hxM : Γ.Adj x M)
    (hML : M ≠ L₀) {t : ZMod (2 * 4) → V} (ht : IsPolygonApartment Γ 4 t)
    (ht4 : t 4 = x) (ht5 : t 5 = L₀) {y : V} (hy : Γ.dist x y = 4) :
    ∃ g : H, g • x = x ∧ g • t 0 = y := by
  classical
  have hyx : Γ.dist y x = 4 := by rw [dist_comm]; exact hy
  have hyM : Γ.dist y M = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy hxM
  let a := proj hP hyM
  have haM : Γ.Adj M a := by simpa [a] using proj_adj hP hyM
  have hya : Γ.dist y a = 2 := by simpa [a] using proj_dist hP hyM
  let K := commonNeighbor hP hya
  have hKy : Γ.Adj y K := by simpa [K] using commonNeighbor_adj_left hP hya
  have hKa : Γ.Adj a K := by simpa [K] using commonNeighbor_adj_right hP hya
  have hKM : K ≠ M := by
    intro hKM
    have hyM' : Γ.Adj y M := by rwa [hKM] at hKy
    have hxM1 : Γ.dist x M = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxM
    have hMy1 : Γ.dist M y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyM'.symm
    have hle : Γ.dist x y ≤ 2 := by
      calc
        Γ.dist x y ≤ Γ.dist x M + Γ.dist M y := hP.connected.dist_triangle
        _ = 2 := by rw [hxM1, hMy1]
    omega
  have hya_ne : y ≠ a := by
    intro h
    rw [h] at hya
    rw [SimpleGraph.dist_self] at hya
    omega
  have hax : a ≠ x := by
    intro h
    rw [h] at hya
    omega
  let z : ℤ → V := fun s =>
    if s = 0 then y else if s = 1 then K else if s = 2 then a
      else if s = 3 then M else if s = 4 then x else L₀
  have hadj : ∀ s : ℤ, 0 ≤ s → s ≤ 4 → Γ.Adj (z s) (z (s + 1)) := by
    intro s hs0 hs4
    interval_cases s
    · simpa [z] using hKy
    · simpa [z] using hKa.symm
    · simpa [z] using haM.symm
    · simpa [z] using hxM.symm
    · simpa [z] using hxL₀
  have hnb : ∀ s : ℤ, 0 ≤ s → s + 2 ≤ 4 + 1 → z s ≠ z (s + 2) := by
    intro s hs0 hs2
    have hs3 : s ≤ 3 := by omega
    interval_cases s
    · simpa [z] using hya_ne
    · simpa [z] using hKM
    · simpa [z] using hax
    · simpa [z] using hML
  have hzb : z 4 = apt t 4 := by simpa [z, apt] using ht4.symm
  have hzb1 : z ((4 : ℤ) + 1) = apt t ((4 : ℤ) + 1) := by
    have h5 : ((4 : ℤ) + 1) = 5 := by norm_num
    rw [h5]
    simpa [z, apt] using ht5.symm
  obtain ⟨g, -, hgfix, hgz⟩ :=
    exists_smul_apt_path (D := H) (n := 4) (t := t) ht (by norm_num) hM
      (a := (0 : ℤ)) (b := (4 : ℤ)) (by norm_num) (by norm_num) z hzb hzb1 hadj hnb
  refine ⟨g, ?_, ?_⟩
  · simpa [ht4, apt] using hgfix
  · have h0 := hgz 0 (by norm_num) (by norm_num)
    simpa [z, apt] using h0


private theorem exists_smul_eq_of_dist_eq_four_faithful (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (hM : MoufangCondition H Γ 4) {x y y' : V} (hy : Γ.dist x y = 4)
    (hy' : Γ.dist x y' = 4) : ∃ g : H, g • x = x ∧ g • y = y' := by
  classical
  obtain ⟨M, hxM, -⟩ := exists_adj_ne_two hT x x x
  obtain ⟨L₀, hxL₀, -, hL₀M⟩ := exists_adj_ne_two hT x x M
  obtain ⟨t, ht, ht4, ht5⟩ :=
    exists_polygonApartment_through_edge (Γ := Γ) (n := 4) (by norm_num) hP hT
      (v := x) (u := L₀) hxL₀
  obtain ⟨g₁, hg₁x, hg₁y⟩ :=
    exists_smul_fix_of_dist_eq_four hP hT hM hxL₀ hxM hL₀M.symm ht ht4 ht5 hy
  obtain ⟨g₂, hg₂x, hg₂y⟩ :=
    exists_smul_fix_of_dist_eq_four hP hT hM hxL₀ hxM hL₀M.symm ht ht4 ht5 hy'
  have hxinv : g₁⁻¹ • x = x := by
    simpa using (congrArg (fun v => g₁⁻¹ • v) hg₁x).symm
  have hyinv : g₁⁻¹ • y = t 0 := by
    simpa using (congrArg (fun v => g₁⁻¹ • v) hg₁y).symm
  refine ⟨g₂ * g₁⁻¹, ?_, ?_⟩
  · calc
      (g₂ * g₁⁻¹) • x = g₂ • (g₁⁻¹ • x) := by rw [mul_smul]
      _ = g₂ • x := by rw [hxinv]
      _ = x := hg₂x
  · calc
      (g₂ * g₁⁻¹) • y = g₂ • (g₁⁻¹ • y) := by rw [mul_smul]
      _ = g₂ • (t 0) := by rw [hyinv]
      _ = y' := hg₂y

end StabilizerTransitive

section StabilizerTransitiveGeneral

variable {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

theorem exists_smul_eq_of_dist_eq_four (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) {x y y' : V} (hy : Γ.dist x y = 4)
    (hy' : Γ.dist x y' = 4) : ∃ g : H, g • x = x ∧ g • y = y' := by
  classical
  let φ : H →* Equiv.Perm V := MulAction.toPermHom H V
  have hKgraph : GraphAction φ.range Γ := by
    refine ⟨fun k a b => ?_⟩
    obtain ⟨g, hg⟩ := k.2
    have hka : k • a = g • a := by
      rw [Subgroup.smul_def]
      change (k : Equiv.Perm V) a = g • a
      rw [← hg]
      rfl
    have hkb : k • b = g • b := by
      rw [Subgroup.smul_def]
      change (k : Equiv.Perm V) b = g • b
      rw [← hg]
      rfl
    rw [hka, hkb]
    exact GraphAction.adj_smul g a b
  haveI : GraphAction φ.range Γ := hKgraph
  have hMK : MoufangCondition φ.range Γ 4 := by
    intro p hp u v hu hv hne hne'
    obtain ⟨g, hfix, hgu⟩ := hM p hp u v hu hv hne hne'
    have hφ : ∀ v : V, (φ g : Equiv.Perm V) v = g • v := by
      intro v
      simp [φ]
    refine ⟨⟨φ g, MonoidHom.mem_range.2 ⟨g, rfl⟩⟩, ?_, ?_⟩
    · intro i hi1 hi2 w hw
      rw [Subgroup.smul_def]
      change (φ g : Equiv.Perm V) w = w
      rw [hφ]
      exact hfix i hi1 hi2 w hw
    · rw [Subgroup.smul_def]
      change (φ g : Equiv.Perm V) u = v
      rw [hφ]
      exact hgu
  haveI : FaithfulSMul φ.range V := inferInstance
  obtain ⟨k, hkx, hky⟩ :=
    exists_smul_eq_of_dist_eq_four_faithful (H := φ.range) hP hT hMK hy hy'
  obtain ⟨g, hg⟩ := k.2
  have hkx' : g • x = x := by
    have hk : k • x = g • x := by
      rw [Subgroup.smul_def]
      change (k : Equiv.Perm V) x = g • x
      rw [← hg]
      rfl
    rwa [hk] at hkx
  have hky' : g • y = y' := by
    have hk : k • y = g • y := by
      rw [Subgroup.smul_def]
      change (k : Equiv.Perm V) y = g • y
      rw [← hg]
      rfl
    rwa [hk] at hky
  exact ⟨g, hkx', hky'⟩

end StabilizerTransitiveGeneral

section OppositePairs

variable {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

theorem exists_smul_eq_smul_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) (c : Γ.Coloring (Fin 2)) {x y x' y' : V}
    (h : Γ.dist x y = 4) (h' : Γ.dist x' y' = 4) (hc : c x = c x') :
    ∃ g : H, g • x = x' ∧ g • y = y' := by
  classical
  obtain ⟨g₁, hg₁⟩ := exists_smul_eq_of_color_eq hP hT hM c hc
  have hdist : Γ.dist (g₁ • x) (g₁ • y) = Γ.dist x y := GPath.dist_smul hP.connected g₁ x y
  have hy₂ : Γ.dist x' (g₁ • y) = 4 := by
    rw [hg₁, h] at hdist
    exact hdist
  obtain ⟨g₂, hg₂x, hg₂y⟩ := exists_smul_eq_of_dist_eq_four hP hT hM hy₂ h'
  refine ⟨g₂ * g₁, ?_, ?_⟩
  · calc
      (g₂ * g₁) • x = g₂ • (g₁ • x) := by rw [mul_smul]
      _ = g₂ • x' := by rw [hg₁]
      _ = x' := hg₂x
  · calc
      (g₂ * g₁) • y = g₂ • (g₁ • y) := by rw [mul_smul]
      _ = y' := hg₂y

theorem ncard_spanSet_eq_of_color_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) (c : Γ.Coloring (Fin 2)) {x y x' y' : V}
    (h : Γ.dist x y = 4) (h' : Γ.dist x' y' = 4) (hc : c x = c x') :
    (spanSet Γ x y).ncard = (spanSet Γ x' y').ncard := by
  obtain ⟨g, hgx, hgy⟩ := exists_smul_eq_smul_eq hP hT hM c h h' hc
  calc
    (spanSet Γ x y).ncard = (g • spanSet Γ x y).ncard := (Set.ncard_smul_set g _).symm
    _ = (spanSet Γ (g • x) (g • y)).ncard := by rw [smul_spanSet hP.connected]
    _ = (spanSet Γ x' y').ncard := by rw [hgx, hgy]

end OppositePairs

end CFSG.Geometry.GeneralizedQuadrangles

module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.RootGroups
public import CFSG.Geometry.GeneralizedQuadrangles.Counting.Variance
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth
open scoped Pointwise

universe u v

variable {V : Type u} {Γ : SimpleGraph V}

section Equivariance

variable {H : Type v} [Group H] [MulAction H V] [GraphAction H Γ]

theorem smul_perpSet (hΓ : Γ.Connected) (g : H) (x : V) :
    g • perpSet Γ x = perpSet Γ (g • x) := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_perpSet, mem_perpSet]
  constructor
  · intro hz
    calc Γ.dist (g • x) z = Γ.dist (g • x) (g • (g⁻¹ • z)) := by simp
      _ = Γ.dist x (g⁻¹ • z) := GPath.dist_smul hΓ g x (g⁻¹ • z)
      _ ≤ 2 := hz
  · intro hz
    calc Γ.dist x (g⁻¹ • z) = Γ.dist (g • x) (g • (g⁻¹ • z)) :=
          (GPath.dist_smul hΓ g x (g⁻¹ • z)).symm
      _ = Γ.dist (g • x) z := by simp
      _ ≤ 2 := hz

end Equivariance

section SpanTrace

variable [Fintype V] [DecidableRel Γ.Adj]

theorem spanSet_subset_traceSet_of_mem_trace (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {a b C D : V} (hab : Γ.dist a b = 4) (hC : C ∈ traceSet Γ a b)
    (hD : D ∈ traceSet Γ a b) : spanSet Γ a b ⊆ traceSet Γ C D := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rw [dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT hab hz hC
  · rw [dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT hab hz hD

end SpanTrace

section Transversals

variable [Fintype V] [DecidableRel Γ.Adj]

theorem spanSet_eq_traceSet_of_isRegularVertex (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {L K x y Na Nb : V} (hL : IsRegularVertex Γ L) (hLK : Γ.dist L K = 4)
    (hxL : Γ.Adj L x) (hyL : Γ.Adj L y) (hxy : x ≠ y)
    (hxNa : Γ.Adj x Na) (hyNb : Γ.Adj y Nb)
    (hNaK : ∃ a, Γ.Adj K a ∧ Γ.Adj Na a)
    (hNbK : ∃ b, Γ.Adj K b ∧ Γ.Adj Nb b) :
    Γ.dist Na Nb = 4 ∧ spanSet Γ Na Nb = traceSet Γ L K := by
  classical
  obtain ⟨a, haK, haNa⟩ := hNaK
  obtain ⟨b, hbK, hbNb⟩ := hNbK
  have hxy2 : Γ.dist x y = 2 := dist_eq_two_of_adj_of_adj_of_ne hP hxL.symm hyL hxy
  have hNa_ne_L : Na ≠ L := by
    intro h
    have hLa : Γ.Adj L a := h ▸ haNa
    have h1 : Γ.dist L a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hLa
    have h2 : Γ.dist a K = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr haK.symm
    have h3 : Γ.dist L K ≤ Γ.dist L a + Γ.dist a K :=
      hP.connected.dist_triangle (u := L) (v := a) (w := K)
    omega
  have hNb_ne_L : Nb ≠ L := by
    intro h
    have hLb : Γ.Adj L b := h ▸ hbNb
    have h1 : Γ.dist L b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hLb
    have h2 : Γ.dist b K = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbK.symm
    have h3 : Γ.dist L K ≤ Γ.dist L b + Γ.dist b K :=
      hP.connected.dist_triangle (u := L) (v := b) (w := K)
    omega
  have hNaL : Γ.dist Na L = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hxNa.symm hxL.symm hNa_ne_L
  have hNbL : Γ.dist Nb L = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hyNb.symm hyL.symm hNb_ne_L
  have hKNa : Γ.dist K Na = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP haK haNa.symm (by
      intro h
      rw [h] at hLK
      rw [SimpleGraph.dist_comm] at hLK
      omega)
  have hKNb : Γ.dist K Nb = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hbK hbNb.symm (by
      intro h
      rw [h] at hLK
      rw [SimpleGraph.dist_comm] at hLK
      omega)
  have hNaNb : Na ≠ Nb := by
    intro h
    have hyNa : Γ.Adj y Na := h ▸ hyNb
    have hNa_common : Γ.Adj x Na ∧ Γ.Adj y Na := ⟨hxNa, hyNa⟩
    have hL_common : Γ.Adj x L ∧ Γ.Adj y L := ⟨hxL.symm, hyL.symm⟩
    exact hNa_ne_L ((existsUnique_commonNeighbor hP hxy2).unique hNa_common hL_common)
  have hNa_mem : Na ∈ traceSet Γ L K :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hNaL, hKNa⟩
  have hNb_mem : Nb ∈ traceSet Γ L K :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hNbL, hKNb⟩
  have hNaNb4 : Γ.dist Na Nb = 4 :=
    dist_eq_four_of_mem_trace hP hLK hNa_mem hNb_mem hNaNb
  have hL_mem : L ∈ traceSet Γ Na Nb := ⟨hNaL, hNbL⟩
  have hK_mem : K ∈ traceSet Γ Na Nb :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hKNa,
      by rw [SimpleGraph.dist_comm]; exact hKNb⟩
  have hsub1 : spanSet Γ Na Nb ⊆ traceSet Γ L K :=
    spanSet_subset_traceSet_of_mem_trace hP hT hNaNb4 hL_mem hK_mem
  have hsub2 : spanSet Γ L K ⊆ traceSet Γ Na Nb :=
    spanSet_subset_traceSet_of_mem_trace hP hT hLK hNa_mem hNb_mem
  have hcard1 : (spanSet Γ L K).ncard = Γ.degree L := hL K hLK
  have hcard2 : (traceSet Γ Na Nb).ncard = Γ.degree Na := ncard_trace hP hNaNb4
  have hdeg : Γ.degree L = Γ.degree Na :=
    hP.degree_eq_of_adj_of_adj (by norm_num) hT hxL.symm hxNa
  have hcard : (traceSet Γ Na Nb).ncard = (spanSet Γ L K).ncard := by
    rw [hcard2, ← hdeg, ← hcard1]
  have hspan_eq : spanSet Γ L K = traceSet Γ Na Nb :=
    Set.eq_of_subset_of_ncard_le hsub2 (le_of_eq hcard)
  have hsub3 : traceSet Γ L K ⊆ spanSet Γ Na Nb := by
    intro M hM
    rw [mem_spanSet]
    intro P hP
    have hP' : P ∈ spanSet Γ L K := by rw [hspan_eq]; exact hP
    rw [mem_spanSet] at hP'
    have hle : Γ.dist P M ≤ 2 := hP' M hM
    rwa [SimpleGraph.dist_comm] at hle
  exact ⟨hNaNb4, Set.Subset.antisymm hsub1 hsub3⟩

end Transversals

section RegularLine

variable [Fintype V] [DecidableRel Γ.Adj]
variable {H : Type v} [Group H] [MulAction H V] [GraphAction H Γ]

theorem rootGroup_le_symmetryGroup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {x L y : V} (hL : IsRegularVertex Γ L) (hx : Γ.Adj L x) (hy : Γ.Adj L y) (hxy : x ≠ y) :
    rootGroup H Γ x L y ≤ symmetryGroup H Γ L := by
  intro g hg
  rw [mem_symmetryGroup, mem_fixingSubgroup_iff]
  intro z hz
  rw [mem_perpSet] at hz
  have hgx := (mem_rootGroup H).mp hg
  have hgL : g ∈ fixingSubgroup H (Γ.neighborSet L) := hgx.2.1
  rcases (by omega : Γ.dist L z = 0 ∨ Γ.dist L z = 1 ∨ Γ.dist L z = 2) with h0 | h1 | h2
  · have hzL : z = L := by
      rw [SimpleGraph.dist_comm] at h0
      exact (hP.connected.dist_eq_zero_iff).mp h0
    rw [hzL]
    exact (mem_fixingSubgroup_iff H).mp hgx.1 L hx.symm
  · exact (mem_fixingSubgroup_iff H).mp hgL z (SimpleGraph.dist_eq_one_iff_adj.mp h1)
  ·
    let u := commonNeighbor hP h2
    have huL : Γ.Adj L u := commonNeighbor_adj_left hP h2
    have hzu : Γ.Adj z u := commonNeighbor_adj_right hP h2
    have hgu : g • u = u := (mem_fixingSubgroup_iff H).mp hgL u huL
    have hdeg : ∀ v : V, 3 ≤ Nat.card (Γ.neighborSet v) := by
      intro v
      rw [Nat.card_coe_set_eq, SimpleGraph.ncard_neighborSet]
      exact hT v
    obtain ⟨w, hzw, hwu⟩ := CFSG.Quasithin.H13.F431.F45.exists_nbr_ne_of_card (hdeg z) u
    obtain ⟨K, hwK, hKz⟩ := CFSG.Quasithin.H13.F431.F45.exists_nbr_ne_of_card (hdeg w) z
    have hwL : Γ.dist w L = 3 := by
      rcases hP.dist_adj hzw L with h | h
      · rw [h2] at h
        rw [SimpleGraph.dist_comm]
        omega
      · rw [h2] at h
        exfalso
        have h1 : Γ.dist L w = 1 := by omega
        have hLw : Γ.Adj L w := SimpleGraph.dist_eq_one_iff_adj.mp h1
        exact hwu ((existsUnique_commonNeighbor hP h2).unique ⟨hLw, hzw⟩ ⟨huL, hzu⟩)
    have hwL' : Γ.dist L w = 3 := by rw [SimpleGraph.dist_comm]; exact hwL
    have hKL : Γ.dist K L = 4 := by
      rcases hP.dist_adj hwK L with h | h
      · rw [hwL'] at h
        rw [SimpleGraph.dist_comm]
        omega
      · rw [hwL'] at h
        exfalso
        have hKL2 : Γ.dist L K = 2 := by omega
        let p := commonNeighbor hP hKL2
        have hpL : Γ.Adj L p := commonNeighbor_adj_left hP hKL2
        have hpK : Γ.Adj K p := commonNeighbor_adj_right hP hKL2
        have hwp : Γ.dist w p = 2 := by
          have hne : w ≠ p := by
            intro hwp'
            rw [← hwp'] at hpL
            have h1 : Γ.dist L w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hpL
            rw [SimpleGraph.dist_comm] at hwL
            omega
          exact dist_eq_two_of_adj_of_adj_of_ne hP hwK hpK hne
        have hwu2 : Γ.dist w u = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP hzw.symm hzu hwu
        have hpu : p = u :=
          (existsUnique_proj hP hwL).unique
            ⟨hpL, hwp⟩ ⟨huL, hwu2⟩
        have hKu : Γ.Adj u K := by rw [← hpu]; exact hpK.symm
        exact hKz ((existsUnique_commonNeighbor hP hwu2).unique
          ⟨hwK, hKu⟩ ⟨hzw.symm, hzu.symm⟩)
    have hxK : Γ.dist x K = 3 := by
      rcases hP.dist_adj hx K with h | h
      · rw [hKL] at h
        have h5 := hP.dist_le (by norm_num) K x
        omega
      · rw [hKL] at h
        rw [SimpleGraph.dist_comm]
        omega
    let a := proj hP hxK
    have haK : Γ.Adj K a := proj_adj hP hxK
    have hxa : Γ.dist x a = 2 := proj_dist hP hxK
    let Na := commonNeighbor hP hxa
    have hxNa : Γ.Adj x Na := commonNeighbor_adj_left hP hxa
    have haNa : Γ.Adj Na a := (commonNeighbor_adj_right hP hxa).symm
    have hyK : Γ.dist y K = 3 := by
      rcases hP.dist_adj hy K with h | h
      · rw [hKL] at h
        have h5 := hP.dist_le (by norm_num) K y
        omega
      · rw [hKL] at h
        rw [SimpleGraph.dist_comm]
        omega
    let b := proj hP hyK
    have hbK : Γ.Adj K b := proj_adj hP hyK
    have hyb : Γ.dist y b = 2 := proj_dist hP hyK
    let Nb := commonNeighbor hP hyb
    have hyNb : Γ.Adj y Nb := commonNeighbor_adj_left hP hyb
    have hbNb : Γ.Adj Nb b := (commonNeighbor_adj_right hP hyb).symm
    obtain ⟨hNaNb4, hspan⟩ :=
      spanSet_eq_traceSet_of_isRegularVertex hP hT hL
        (by rw [SimpleGraph.dist_comm]; exact hKL) hx hy hxy hxNa hyNb
        ⟨a, haK, haNa⟩ ⟨b, hbK, hbNb⟩
    have hzK : Γ.dist K z = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hwK.symm hzw.symm (by
        intro h
        rw [← h] at h2
        rw [SimpleGraph.dist_comm] at h2
        omega)
    have hz_trace : z ∈ traceSet Γ L K := ⟨h2, hzK⟩
    have hz_span : z ∈ spanSet Γ Na Nb := by rw [hspan]; exact hz_trace
    have hgNa : g • Na = Na := (mem_fixingSubgroup_iff H).mp hgx.1 Na hxNa
    have hgNb : g • Nb = Nb := (mem_fixingSubgroup_iff H).mp hgx.2.2 Nb hyNb
    have hgz_span : g • z ∈ spanSet Γ Na Nb := by
      rw [mem_spanSet]
      intro v hv
      have hv' : g⁻¹ • v ∈ traceSet Γ Na Nb := by
        refine ⟨?_, ?_⟩
        · calc Γ.dist Na (g⁻¹ • v) = Γ.dist (g • Na) (g • (g⁻¹ • v)) :=
                (GPath.dist_smul hP.connected g Na (g⁻¹ • v)).symm
            _ = Γ.dist Na v := by rw [hgNa]; simp
            _ = 2 := hv.1
        · calc Γ.dist Nb (g⁻¹ • v) = Γ.dist (g • Nb) (g • (g⁻¹ • v)) :=
                (GPath.dist_smul hP.connected g Nb (g⁻¹ • v)).symm
            _ = Γ.dist Nb v := by rw [hgNb]; simp
            _ = 2 := hv.2
      have hle : Γ.dist z (g⁻¹ • v) ≤ 2 := hz_span (g⁻¹ • v) hv'
      calc Γ.dist (g • z) v = Γ.dist (g • z) (g • (g⁻¹ • v)) := by simp
        _ = Γ.dist z (g⁻¹ • v) := GPath.dist_smul hP.connected g z (g⁻¹ • v)
        _ ≤ 2 := hle
    have hgzu : Γ.Adj u (g • z) := by
      have h1 : Γ.Adj (g • z) (g • u) := (GraphAction.adj_smul g z u).mpr hzu
      rw [hgu] at h1
      exact h1.symm
    have huniq := ncard_spanSet_inter_neighborSet_le_one hP hT hNaNb4 u
    rw [Set.ncard_le_one] at huniq
    exact (huniq z ⟨hz_span, hzu.symm⟩ (g • z) ⟨hgz_span, hgzu⟩).symm

theorem symmetryGroup_le_rootGroup {x L y : V} (hx : Γ.Adj L x) (hy : Γ.Adj L y) :
    symmetryGroup H Γ L ≤ rootGroup H Γ x L y := by
  intro g hg
  have hg' := (mem_fixingSubgroup_iff H).mp hg
  rw [mem_rootGroup]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_fixingSubgroup_iff]
    intro M hM
    exact hg' M (by
      rw [mem_perpSet]
      exact SimpleGraph.dist_le (SimpleGraph.Walk.cons hx (SimpleGraph.Walk.cons hM
        SimpleGraph.Walk.nil)))
  · rw [mem_fixingSubgroup_iff]
    intro M hM
    have hLM : Γ.Adj L M := hM
    exact hg' M (by rw [mem_perpSet, SimpleGraph.dist_eq_one_iff_adj.mpr hLM]; norm_num)
  · rw [mem_fixingSubgroup_iff]
    intro M hM
    exact hg' M (by
      rw [mem_perpSet]
      exact SimpleGraph.dist_le (SimpleGraph.Walk.cons hy (SimpleGraph.Walk.cons hM
        SimpleGraph.Walk.nil)))

theorem rootGroup_eq_symmetryGroup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {x L y : V} (hL : IsRegularVertex Γ L) (hx : Γ.Adj L x) (hy : Γ.Adj L y) (hxy : x ≠ y) :
    rootGroup H Γ x L y = symmetryGroup H Γ L :=
  le_antisymm (rootGroup_le_symmetryGroup hP hT hL hx hy hxy)
    (symmetryGroup_le_rootGroup hx hy)

end RegularLine

section ConcurrentSymmetries

variable [Fintype V] [DecidableRel Γ.Adj]
variable {H : Type v} [Group H] [MulAction H V] [GraphAction H Γ] [FaithfulSMul H V]

theorem commute_of_mem_symmetryGroup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {L L' : V} (hLL' : Γ.dist L L' = 2) {g h : H}
    (hg : g ∈ symmetryGroup H Γ L) (hh : h ∈ symmetryGroup H Γ L') : Commute g h := by
  classical
  have hg' : ∀ z ∈ perpSet Γ L, g • z = z := (mem_fixingSubgroup_iff H).mp hg
  have hh' : ∀ z ∈ perpSet Γ L', h • z = z := (mem_fixingSubgroup_iff H).mp hh
  have hL'L : L' ∈ perpSet Γ L := by rw [mem_perpSet]; exact le_of_eq hLL'
  have hLL'mem : L ∈ perpSet Γ L' := by
    rw [mem_perpSet, SimpleGraph.dist_comm]; exact le_of_eq hLL'
  have hgL' : g • L' = L' := hg' L' hL'L
  have hhL : h • L = L := hh' L hLL'mem
  have hnorm_g : ∀ k ∈ symmetryGroup H Γ L', g * k * g⁻¹ ∈ symmetryGroup H Γ L' := by
    intro k hk
    have hset : g • perpSet Γ L' = perpSet Γ L' := by
      rw [smul_perpSet hP.connected g L', hgL']
    have hmem := Set.conj_mem_fixingSubgroup (M := H) (g := g) (t := perpSet Γ L')
      (s := perpSet Γ L') hset hk
    simpa [MulAut.conj_apply] using hmem
  have hnorm_h : ∀ k ∈ symmetryGroup H Γ L, h * k * h⁻¹ ∈ symmetryGroup H Γ L := by
    intro k hk
    have hset : h • perpSet Γ L = perpSet Γ L := by
      rw [smul_perpSet hP.connected h L, hhL]
    have hmem := Set.conj_mem_fixingSubgroup (M := H) (g := h) (t := perpSet Γ L)
      (s := perpSet Γ L) hset hk
    simpa [MulAut.conj_apply] using hmem
  have hkL : g * h * g⁻¹ * h⁻¹ ∈ symmetryGroup H Γ L := by
    have h1 : h * g⁻¹ * h⁻¹ ∈ symmetryGroup H Γ L := hnorm_h g⁻¹ (Subgroup.inv_mem _ hg)
    simpa only [mul_assoc] using Subgroup.mul_mem _ hg h1
  have hkL' : g * h * g⁻¹ * h⁻¹ ∈ symmetryGroup H Γ L' := by
    have h1 : g * h * g⁻¹ ∈ symmetryGroup H Γ L' := hnorm_g h hh
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hh)
  let u := commonNeighbor hP hLL'
  have hu : Γ.Adj L u := commonNeighbor_adj_left hP hLL'
  have hu' : Γ.Adj L' u := commonNeighbor_adj_right hP hLL'
  have hdeg : ∀ v : V, 3 ≤ Nat.card (Γ.neighborSet v) := by
    intro v
    rw [Nat.card_coe_set_eq, SimpleGraph.ncard_neighborSet]
    exact hT v
  obtain ⟨a, haL, hau⟩ := CFSG.Quasithin.H13.F431.F45.exists_nbr_ne_of_card (hdeg L) u
  obtain ⟨x', hxL', hxu⟩ := CFSG.Quasithin.H13.F431.F45.exists_nbr_ne_of_card (hdeg L') u
  obtain ⟨w, hxw, hwL'⟩ := CFSG.Quasithin.H13.F431.F45.exists_nbr_ne_of_card (hdeg x') L'
  let p : GPath Γ 4 :=
    { toFun := fun i => if i = 0 then a else if i = 1 then L else if i = 2 then u
        else if i = 3 then L' else x'
      adj := fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
        · simpa using haL.symm
        · simpa using hu
        · simpa using hu'.symm
        · simpa using hxL'
      tail := fun i hi => by
        have h0 : i ≠ 0 := by omega
        have h1 : i ≠ 1 := by omega
        have h2 : i ≠ 2 := by omega
        have h3 : i ≠ 3 := by omega
        simp [h0, h1, h2, h3] }
  have hp0 : p 0 = a := by simp [p]
  have hp1 : p 1 = L := by simp [p]
  have hp2 : p 2 = u := by simp [p]
  have hp3 : p 3 = L' := by simp [p]
  have hp4 : p 4 = x' := by simp [p]
  have hp : p.NoBack := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [hp0, hp2]; exact hau
    · rw [hp1, hp3]
      intro h
      rw [h] at hLL'
      simp at hLL'
    · rw [hp2, hp4]; exact Ne.symm hxu
  have hfixL := (mem_fixingSubgroup_iff H).mp hkL
  have hfixL' := (mem_fixingSubgroup_iff H).mp hkL'
  have hfixΓ : ∀ i, 1 ≤ i → i ≤ 3 → ∀ v, Γ.Adj (p i) v →
      (g * h * g⁻¹ * h⁻¹) • v = v := by
    intro i hi1 hi3 v hv
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · rw [hp1] at hv
      exact hfixL v (by
        rw [mem_perpSet, SimpleGraph.dist_eq_one_iff_adj.mpr hv]
        norm_num)
    · rw [hp2] at hv
      exact hfixL v (by
        rw [mem_perpSet]
        simpa using SimpleGraph.dist_le (SimpleGraph.Walk.cons hu
          (SimpleGraph.Walk.cons hv SimpleGraph.Walk.nil)))
    · rw [hp3] at hv
      exact hfixL' v (by
        rw [mem_perpSet, SimpleGraph.dist_eq_one_iff_adj.mpr hv]
        norm_num)
  have hgw : (g * h * g⁻¹ * h⁻¹) • w = w :=
    hfixL' w (by
      rw [mem_perpSet]
      simpa using SimpleGraph.dist_le (SimpleGraph.Walk.cons hxL'
        (SimpleGraph.Walk.cons hxw SimpleGraph.Walk.nil)))
  have hpg : IsGenPolygon Γ 4 := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hTh : ∀ v : V, 3 ≤ (Γ.neighborSet v).encard := three_le_encard_of_isThick hT
  have hall : ∀ v : V, (g * h * g⁻¹ * h⁻¹) • v = v :=
    hpg.smul_eq_of_fix_root (by omega) hTh p hp hfixΓ (by simpa [hp4] using hxw)
      (by simpa [hp3] using hwL') hgw
  have hk : g * h * g⁻¹ * h⁻¹ = 1 :=
    eq_of_smul_eq_smul (m₁ := g * h * g⁻¹ * h⁻¹) (m₂ := 1) (fun v => by
      rw [one_smul]
      exact hall v)
  rw [commute_iff_eq]
  calc g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by group
    _ = h * g := by rw [hk, one_mul]

end ConcurrentSymmetries

section RegularVertex

variable [Fintype V] [DecidableRel Γ.Adj]

@[expose] def dualColoring (c : Γ.Coloring (Fin 2)) : Γ.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (fun v => 1 - c v) (by
    intro v w h
    have hne := c.valid h
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c v) with hv | hv <;> rcases hfin (c w) with hw | hw
    · exact absurd (hv.trans hw.symm) hne
    · rw [hv, hw]; simp
    · rw [hv, hw]; simp
    · exact absurd (hv.trans hw.symm) hne)

@[simp] theorem dualColoring_apply (c : Γ.Coloring (Fin 2)) (v : V) :
    dualColoring c v = 1 - c v := rfl

theorem degree_eq_of_dualColoring {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (v : V) :
    Γ.degree v = if dualColoring c v = 0 then s + 1 else t + 1 := by
  have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rw [dualColoring_apply]
  rcases hfin (c v) with hv | hv
  · rw [hdeg, if_pos hv]
    rw [if_neg (by rw [hv]; decide)]
  · rw [hdeg, if_neg (by rw [hv]; decide)]
    rw [if_pos (by rw [hv]; decide)]

theorem t_le_s_of_isRegularVertex (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x : V}
    (hx : c x = 0) (hreg : IsRegularVertex Γ x) : t ≤ s := by
  classical
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
    rw [h1, hreg y hxy, hdeg x, if_pos hx]
  have hXsub : (X : Set V) ⊆ spanSet Γ x y := by
    intro z hz
    simpa [X] using hz
  have hm : 2 ≤ X.card := by
    have h2 := two_le_t hP hT c hdeg
    rw [hXcard]
    omega
  exact t_le_s_of_card_eq_t_add_one hP hT c hdeg hx hxy hXsub hm hXcard

end RegularVertex

section RegularLineOrder

theorem card_symmetryGroup {V₀ : Type} {Γ₀ : SimpleGraph V₀} {H₀ : Type} [Fintype V₀]
    [DecidableRel Γ₀.Adj] [Group H₀] [MulAction H₀ V₀] [GraphAction H₀ Γ₀]
    [FaithfulSMul H₀ V₀] (hP : IsGeneralizedPolygon Γ₀ 4) (hT : IsThick Γ₀)
    (hM : MoufangCondition H₀ Γ₀ 4) {x L y : V₀} (hL : IsRegularVertex Γ₀ L)
    (hx : Γ₀.Adj L x) (hy : Γ₀.Adj L y) (hxy : x ≠ y) :
    Nat.card (symmetryGroup H₀ Γ₀ L) = Γ₀.degree L - 1 := by
  classical
  have hdeg : ∀ v : V₀, 3 ≤ Nat.card (Γ₀.neighborSet v) := by
    intro v
    rw [Nat.card_coe_set_eq, SimpleGraph.ncard_neighborSet]
    exact hT v
  obtain ⟨p0, hxp0, hp0L⟩ := CFSG.Quasithin.H13.F431.F45.exists_nbr_ne_of_card (hdeg x) L
  obtain ⟨p4, hyp4, hp4L⟩ := CFSG.Quasithin.H13.F431.F45.exists_nbr_ne_of_card (hdeg y) L
  let p : GPath Γ₀ 4 :=
    { toFun := fun i => if i = 0 then p0 else if i = 1 then x else if i = 2 then L
        else if i = 3 then y else p4
      adj := fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
        · simpa using hxp0.symm
        · simpa using hx.symm
        · simpa using hy
        · simpa using hyp4
      tail := fun i hi => by
        have h0 : i ≠ 0 := by omega
        have h1 : i ≠ 1 := by omega
        have h2 : i ≠ 2 := by omega
        have h3 : i ≠ 3 := by omega
        simp [h0, h1, h2, h3] }
  have hp1 : p 1 = x := by simp [p]
  have hp2 : p 2 = L := by simp [p]
  have hp3 : p 3 = y := by simp [p]
  have hp4 : p 4 = p4 := by simp [p]
  have hp : p.NoBack := by
    intro i hi
    have hp0 : p 0 = p0 := by simp [p]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [hp0, hp2]; exact hp0L
    · rw [hp1, hp3]; exact hxy
    · rw [hp2, hp4]; exact Ne.symm hp4L
  have hcard := card_rootGroup hP hT hM p hp
  rw [hp1, hp2, hp3, hp4] at hcard
  rw [hP.degree_eq_of_adj_of_adj (by norm_num) hT hyp4 hy.symm] at hcard
  rw [← rootGroup_eq_symmetryGroup hP hT hL hx hy hxy]
  exact hcard

theorem card_symmetryGroup_eq_s {V₀ : Type} {Γ₀ : SimpleGraph V₀} {H₀ : Type} [Fintype V₀]
    [DecidableRel Γ₀.Adj] [Group H₀] [MulAction H₀ V₀] [GraphAction H₀ Γ₀]
    [FaithfulSMul H₀ V₀] (hP : IsGeneralizedPolygon Γ₀ 4) (hT : IsThick Γ₀)
    (hM : MoufangCondition H₀ Γ₀ 4) (c : Γ₀.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ₀.degree v = if c v = 0 then t + 1 else s + 1) {x L y : V₀}
    (hL : IsRegularVertex Γ₀ L) (hc : c L = 1) (hx : Γ₀.Adj L x) (hy : Γ₀.Adj L y)
    (hxy : x ≠ y) : Nat.card (symmetryGroup H₀ Γ₀ L) = s := by
  rw [card_symmetryGroup hP hT hM hL hx hy hxy]
  have h := hdeg L
  rw [if_neg (by rw [hc]; decide)] at h
  omega

end RegularLineOrder

end CFSG.Geometry.GeneralizedQuadrangles

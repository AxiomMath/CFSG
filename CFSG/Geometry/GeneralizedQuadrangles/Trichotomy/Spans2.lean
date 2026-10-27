module

public import CFSG.Geometry.GeneralizedQuadrangles.Trichotomy.Spans

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section SpanClosure

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem spanSet_subset_spanBlock
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {y : V} (hH : HasPropertyH Γ y) {p : ℕ}
    (hp : ∀ a b : V, c a = 0 → Γ.dist a b = 4 → (spanSet Γ a b).ncard = p + 1)
    {z1 z2 a b : V} (hy0 : c y = 0) (hz10 : c z1 = 0) (hz20 : c z2 = 0)
    (hyz1 : Γ.dist y z1 = 2) (hyz2 : Γ.dist y z2 = 2) (hz1z2 : Γ.dist z1 z2 = 4)
    (ha : a ∈ spanBlock Γ y z1 z2) (hb : b ∈ spanBlock Γ y z1 z2)
    (hab : Γ.dist a b = 4) :
    spanSet Γ a b ⊆ spanBlock Γ y z1 z2 := by
  classical
  unfold spanBlock at ha hb
  obtain ⟨Wa, hyWa, hWaT, hWa_a⟩ := ha
  obtain ⟨Wb, hyWb, hWbT, hWb_b⟩ := hb
  obtain ⟨ta, htaT, hWata⟩ := hWaT
  obtain ⟨tb, htbT, hWbtb⟩ := hWbT
  have hWa1 : c Wa = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hyWa
  have hWb1 : c Wb = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hyWb
  have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hWa1 hWa_a
  have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hWb1 hWb_b
  have hay : a ≠ y := by
    intro hay
    have hby_ne : b ≠ y := by
      intro hby
      rw [hay, hby, SimpleGraph.dist_self] at hab
      omega
    have hyb : Γ.dist y b = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := b) (L := Wb)
        hyWb hWb_b hby_ne.symm
    rw [hay] at hab
    omega
  have hby : b ≠ y := by
    intro hby
    have hay_ne : a ≠ y := by
      intro hay
      rw [hay, hby, SimpleGraph.dist_self] at hab
      omega
    have hya : Γ.dist y a = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := a) (L := Wa)
        hyWa hWa_a hay_ne.symm
    rw [hby] at hab
    rw [SimpleGraph.dist_comm] at hya
    omega
  have hya : Γ.dist y a = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := a) (L := Wa)
      hyWa hWa_a hay.symm
  have hyb : Γ.dist y b = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := b) (L := Wb)
      hyWb hWb_b hby.symm
  have hWa_ne : Wa ≠ Wb := by
    intro hEq
    have hdist2 : Γ.dist a b = 2 := by
      refine dist_eq_two_of_adj_of_adj_of_ne hP (x := a) (y := b) (L := Wa) ?_ ?_ ?_
      · exact hWa_a.symm
      · exact hEq.symm ▸ hWb_b
      · intro hab_eq
        rw [hab_eq, SimpleGraph.dist_self] at hab
        omega
    omega
  have hWa_mem : Wa ∈ linesThrough Γ y (spanSet Γ a b) ∩
      linesThrough Γ y (spanSet Γ z1 z2) := by
    constructor
    · rw [mem_linesThrough]
      exact ⟨hyWa, a, left_mem_spanSet hab, hWa_a⟩
    · rw [mem_linesThrough]
      exact ⟨hyWa, ta, htaT, hWata⟩
  have hWb_mem : Wb ∈ linesThrough Γ y (spanSet Γ a b) ∩
      linesThrough Γ y (spanSet Γ z1 z2) := by
    constructor
    · rw [mem_linesThrough]
      exact ⟨hyWb, b, right_mem_spanSet hab, hWb_b⟩
    · rw [mem_linesThrough]
      exact ⟨hyWb, tb, htbT, hWbtb⟩
  have hlines : linesThrough Γ y (spanSet Γ a b) =
      linesThrough Γ y (spanSet Γ z1 z2) :=
    linesThrough_spanSet_eq_of_two_lines hP hT c hy0 hH hp
      hya hyb hyz1 hyz2 hab hz1z2 hWa_mem hWb_mem hWa_ne
  intro u hu
  have htrace : y ∈ traceSet Γ a b :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hya, by rw [SimpleGraph.dist_comm]; exact hyb⟩
  have huy : Γ.dist u y = 2 :=
    dist_eq_two_of_mem_span_of_mem_trace hP hT hab hu htrace
  let L : V := commonNeighbor hP huy
  have hyL : Γ.Adj y L := commonNeighbor_adj_right hP huy
  have hLu : Γ.Adj L u := (commonNeighbor_adj_left hP huy).symm
  have hLmem : L ∈ linesThrough Γ y (spanSet Γ a b) := by
    rw [mem_linesThrough]
    exact ⟨hyL, u, hu, hLu⟩
  have hLmem' : L ∈ linesThrough Γ y (spanSet Γ z1 z2) := by
    rw [hlines] at hLmem
    exact hLmem
  exact ⟨L, hyL, hLmem'.2, hLu⟩

end SpanClosure

section LinesThroughBlock

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem linesThrough_spanSet_eq_of_common_L
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {b : V} (hH : HasPropertyH Γ b) {p : ℕ}
    (hp : ∀ a b : V, c a = 0 → Γ.dist a b = 4 → (spanSet Γ a b).ncard = p + 1)
    {L M a yb x x' : V}
    (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLb : Γ.Adj L b) (hLx : Γ.Adj L x) (hLx' : Γ.Adj L x')
    (hMyb : Γ.Adj M yb) (hbyb : Γ.dist b yb = 2)
    (hba : Γ.dist b a = 2) (hayb : Γ.dist a yb = 4)
    (hxS : x ∈ spanSet Γ a yb) (hx'ne : x' ≠ b) (hx'yb : Γ.dist x' yb = 4) :
    linesThrough Γ b (spanSet Γ x' yb) = linesThrough Γ b (spanSet Γ a yb) := by
  classical
  have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLb
  have hyb0 : c yb = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMyb
  have hLne : L ≠ commonNeighbor hP hbyb := by
    intro hEq
    have hAdj : Γ.Adj L yb := hEq ▸ (commonNeighbor_adj_right hP hbyb).symm
    exact (not_adj_of_dist_eq_four_of_adj_right hP hLM hMyb) hAdj
  have hbx' : Γ.dist b x' = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := b) (y := x') (L := L)
      hLb.symm hLx' hx'ne.symm
  have hLmem : L ∈ linesThrough Γ b (spanSet Γ x' yb) ∩
      linesThrough Γ b (spanSet Γ a yb) := by
    constructor
    · rw [mem_linesThrough]
      exact ⟨hLb.symm, x', left_mem_spanSet hx'yb, hLx'⟩
    · rw [mem_linesThrough]
      exact ⟨hLb.symm, x, hxS, hLx⟩
  have hVmem : commonNeighbor hP hbyb ∈ linesThrough Γ b (spanSet Γ x' yb) ∩
      linesThrough Γ b (spanSet Γ a yb) := by
    constructor
    · rw [mem_linesThrough]
      exact ⟨commonNeighbor_adj_left hP hbyb, yb, right_mem_spanSet hx'yb,
        (commonNeighbor_adj_right hP hbyb).symm⟩
    · rw [mem_linesThrough]
      exact ⟨commonNeighbor_adj_left hP hbyb, yb, right_mem_spanSet hayb,
        (commonNeighbor_adj_right hP hbyb).symm⟩
  exact linesThrough_spanSet_eq_of_two_lines hP hT c hb0 hH hp
    hbx' hbyb hba hbyb hx'yb hayb hLmem hVmem hLne

end LinesThroughBlock

section Covering

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem card_erase_neighborFinset [DecidableEq V]
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {L b : V} (hL : c L = 1) (hb : Γ.Adj L b) :
    ((Γ.neighborFinset L).erase b).card = s := by
  classical
  rw [Finset.card_erase_of_mem]
  · rw [card_neighborFinset_eq_degree, hdeg L, if_neg (by rw [hL]; decide)]
    omega
  · rw [mem_neighborFinset]
    exact hb

theorem dist_eq_four_of_ne_of_dist_eq_two
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {L M x' b yb : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLb : Γ.Adj L b) (hLx' : Γ.Adj L x') (hMyb : Γ.Adj M yb)
    (hbyb : Γ.dist b yb = 2) (hx'b : x' ≠ b) : Γ.dist x' yb = 4 := by
  classical
  have hx'0 : c x' = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLx'
  have hyb0 : c yb = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMyb
  have heven : Even (Γ.dist x' yb) :=
    (hP.eq_iff_even_dist c x' yb).1 (by simp [hx'0, hyb0])
  have hle : Γ.dist x' yb ≤ 4 := hP.dist_le (by norm_num) x' yb
  have hne0 : Γ.dist x' yb ≠ 0 := by
    intro h0
    have hxy : x' = yb := (hP.connected.dist_eq_zero_iff).mp h0
    have hLM2 : Γ.dist L M = 2 := by
      refine dist_eq_two_of_adj_of_adj_of_ne hP (x := L) (y := M) (L := x') hLx' ?_ ?_
      · rw [hxy]
        exact hMyb.symm
      · intro hLM_eq
        rw [hLM_eq, SimpleGraph.dist_self] at hLM
        omega
    omega
  by_contra hne4
  have hd2 : Γ.dist x' yb = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hybL : Γ.dist yb L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c
      (fun h => (not_adj_of_dist_eq_four_of_adj_right (L := L) (M := M) hP hLM hMyb) h.symm)
      (by rw [hyb0, hL]; decide)
  have hxy2 : Γ.dist yb x' = 2 := by rw [SimpleGraph.dist_comm]; exact hd2
  have hby2 : Γ.dist yb b = 2 := by rw [SimpleGraph.dist_comm]; exact hbyb
  have hEq : x' = b :=
    (existsUnique_proj hP hybL).unique ⟨hLx', hxy2⟩ ⟨hLb, hby2⟩
  exact hx'b hEq

private theorem not_meet_M_of_ne_commonNeighbor
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {L M W b yb : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLb : Γ.Adj L b) (hMyb : Γ.Adj M yb) (hbyb : Γ.dist b yb = 2)
    (hbW : Γ.Adj b W) (hWV : W ≠ commonNeighbor hP hbyb) :
    ¬ ∃ m : V, Γ.Adj M m ∧ Γ.Adj W m := by
  classical
  rintro ⟨m, hmM, hWm⟩
  have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLb
  have hbm_ne : b ≠ m := by
    intro hbm
    exact (not_adj_of_dist_eq_four_of_adj_left (L := L) (M := M) hP hLM hLb)
      (hbm ▸ hmM)
  have hbm : Γ.dist b m = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := b) (y := m) (L := W)
      hbW hWm hbm_ne
  have hbM3 : Γ.dist b M = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c
      (fun h => (not_adj_of_dist_eq_four_of_adj_left (L := L) (M := M) hP hLM hLb) h.symm)
      (by rw [hb0, hM]; decide)
  have hm_eq : yb = m :=
    (existsUnique_proj hP hbM3).unique ⟨hMyb, hbyb⟩ ⟨hmM, hbm⟩
  have hW_yb : Γ.Adj W yb := by
    rw [hm_eq]
    exact hWm
  have hEq : W = commonNeighbor hP hbyb :=
    (existsUnique_commonNeighbor hP hbyb).unique
      ⟨hbW, hW_yb.symm⟩
      ⟨commonNeighbor_adj_left hP hbyb, commonNeighbor_adj_right hP hbyb⟩
  exact hWV hEq

end Covering

section LineCovering

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem blockThrough_subset_spanUnion_of_block_eq [DecidableEq V]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {L M b yb a : V} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLb : Γ.Adj L b) (hMyb : Γ.Adj M yb) (hbyb : Γ.dist b yb = 2)
    (hblocks : ∀ x' : V, Γ.Adj L x' → x' ≠ b →
      linesThrough Γ b (spanSet Γ x' yb) = linesThrough Γ b (spanSet Γ a yb)) :
    blockThrough Γ b (spanSet Γ a yb) ⊆ spanUnion hP L M := by
  classical
  intro u hu
  obtain ⟨W, hbW, hWS, hWu⟩ := hu
  by_cases hub : u = b
  · refine ⟨b, yb, hLb, hMyb, ?_⟩
    rw [spanOrLine_of_dist_eq_two hP hbyb]
    rw [hub]
    exact (commonNeighbor_adj_left hP hbyb).symm
  by_cases hWL : W = L
  · have hLu : Γ.Adj L u := by
      rw [hWL] at hWu
      exact hWu
    have huyb : Γ.dist u yb = 4 :=
      dist_eq_four_of_ne_of_dist_eq_two hP c hL hM hLM hLb hLu hMyb hbyb hub
    refine ⟨u, yb, hLu, hMyb, ?_⟩
    rw [spanOrLine_of_dist_eq_four hP huyb]
    exact left_mem_spanSet huyb
  by_cases hWV : W = commonNeighbor hP hbyb
  · refine ⟨b, yb, hLb, hMyb, ?_⟩
    rw [spanOrLine_of_dist_eq_two hP hbyb]
    rw [hWV] at hWu
    exact hWu
  · have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLb
    have hW1 : c W = 1 := color_eq_one_of_adj_of_color_eq_zero hb0 hbW
    let Ls : Finset V := (Γ.neighborFinset L).erase b
    let Ws : Finset V := (Γ.neighborFinset W).erase b
    have hLcard : Ls.card = s := card_erase_neighborFinset c hdeg hL hLb
    have hWcard : Ws.card = s := card_erase_neighborFinset c hdeg hW1 hbW.symm
    have hWmemS : W ∈ linesThrough Γ b (spanSet Γ a yb) := ⟨hbW, hWS⟩
    have hpick : ∀ x' ∈ Ls, ∃ q : V, q ∈ spanSet Γ x' yb ∧ Γ.Adj W q := by
      intro x' hx'
      rw [Finset.mem_erase, mem_neighborFinset] at hx'
      obtain ⟨hx'b, hLx'⟩ := hx'
      have hEY : Γ.dist x' yb = 4 :=
        dist_eq_four_of_ne_of_dist_eq_two hP c hL hM hLM hLb hLx' hMyb hbyb hx'b
      have hblock := hblocks x' hLx' hx'b
      have hWmemX : W ∈ linesThrough Γ b (spanSet Γ x' yb) := by
        rw [hblock]
        exact hWmemS
      obtain ⟨q, hqS, hWq⟩ := hWmemX.2
      exact ⟨q, hqS, hWq⟩
    let p : V → V := fun x' => if h : x' ∈ Ls then Classical.choose (hpick x' h) else b
    have hpS : ∀ x' (hx' : x' ∈ Ls), p x' ∈ spanSet Γ x' yb := by
      intro x' hx'
      simp only [p, dif_pos hx']
      exact (Classical.choose_spec (hpick x' hx')).1
    have hpW : ∀ x' (hx' : x' ∈ Ls), Γ.Adj W (p x') := by
      intro x' hx'
      simp only [p, dif_pos hx']
      exact (Classical.choose_spec (hpick x' hx')).2
    have hpe : ∀ x' (hx' : x' ∈ Ls), p x' ≠ b := by
      intro x' hx' hpb
      have hx'Ls : x' ∈ Ls := hx'
      rw [Finset.mem_erase, mem_neighborFinset] at hx'
      obtain ⟨hx'b, hLx'⟩ := hx'
      have hEY : Γ.dist x' yb = 4 :=
        dist_eq_four_of_ne_of_dist_eq_two hP c hL hM hLM hLb hLx' hMyb hbyb hx'b
      have hbtrace : b ∈ traceSet Γ x' yb :=
        ⟨by
          rw [SimpleGraph.dist_comm]
          exact dist_eq_two_of_adj_of_adj_of_ne hP (x := b) (y := x') (L := L)
            hLb.symm hLx' hx'b.symm,
         by rw [SimpleGraph.dist_comm]; exact hbyb⟩
      have hbS : b ∉ spanSet Γ x' yb :=
        not_mem_spanSet_of_mem_traceSet hP hT hEY hbtrace
      exact hbS (hpb ▸ hpS x' hx'Ls)
    have hpWs : ∀ x' (hx' : x' ∈ Ls), p x' ∈ Ws := by
      intro x' hx'
      rw [Finset.mem_erase, mem_neighborFinset]
      exact ⟨hpe x' hx', by simpa [mem_neighborFinset] using hpW x' hx'⟩
    have hpinj : ∀ x' ∈ Ls, ∀ x'' ∈ Ls, p x' = p x'' → x' = x'' := by
      intro x' hx' x'' hx'' hEq
      have hx'Ls : x' ∈ Ls := hx'
      have hx''Ls : x'' ∈ Ls := hx''
      by_contra hne
      rw [Finset.mem_erase, mem_neighborFinset] at hx' hx''
      obtain ⟨hx'b, hLx'⟩ := hx'
      obtain ⟨hx''b, hLx''⟩ := hx''
      have hEY : Γ.dist x' yb = 4 :=
        dist_eq_four_of_ne_of_dist_eq_two hP c hL hM hLM hLb hLx' hMyb hbyb hx'b
      have hEY' : Γ.dist x'' yb = 4 :=
        dist_eq_four_of_ne_of_dist_eq_two hP c hL hM hLM hLb hLx'' hMyb hbyb hx''b
      have hz1 : p x' ∈ spanOrLine hP x' yb := by
        rw [spanOrLine_of_dist_eq_four hP hEY]
        exact hpS x' hx'Ls
      have hz2 : p x' ∈ spanOrLine hP x'' yb := by
        rw [hEq, spanOrLine_of_dist_eq_four hP hEY']
        exact hpS x'' hx''Ls
      have hne_pair : (x', yb) ≠ (x'', yb) := by
        intro h
        exact hne (by simpa using congrArg Prod.fst h)
      have hzU := spanOrLine_inter_subset hP hT c hL hM hLM hLx' hLx'' hMyb hMyb
        hne_pair ⟨hz1, hz2⟩
      rcases hzU with hzL | hzM
      · exact hWL (by
          have hbp : Γ.dist b (p x') = 2 :=
            dist_eq_two_of_adj_of_adj_of_ne hP (x := b) (y := p x') (L := L)
              hLb.symm hzL (hpe x' hx'Ls).symm
          exact (existsUnique_commonNeighbor hP hbp).unique
            ⟨hbW, (hpW x' hx'Ls).symm⟩ ⟨hLb.symm, hzL.symm⟩)
      · exact (not_meet_M_of_ne_commonNeighbor hP c hL hM hLM hLb hMyb hbyb hbW hWV)
          ⟨p x', hzM, hpW x' hx'Ls⟩
    have hsub : Ls.image p ⊆ Ws := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨x', hx', rfl⟩ := hq
      exact hpWs x' hx'
    have hcard_img : (Ls.image p).card = Ws.card := by
      rw [Finset.card_image_of_injOn hpinj, hLcard, hWcard]
    have himg : Ls.image p = Ws :=
      Finset.eq_of_subset_of_card_le hsub (ge_of_eq hcard_img)
    have huWs : u ∈ Ws := by
      rw [Finset.mem_erase, mem_neighborFinset]
      exact ⟨hub, by simpa [mem_neighborFinset] using hWu⟩
    rw [← himg] at huWs
    rw [Finset.mem_image] at huWs
    obtain ⟨x', hx', hpx'⟩ := huWs
    rw [Finset.mem_erase, mem_neighborFinset] at hx'
    obtain ⟨hx'b, hLx'⟩ := hx'
    have hEY : Γ.dist x' yb = 4 :=
      dist_eq_four_of_ne_of_dist_eq_two hP c hL hM hLM hLb hLx' hMyb hbyb hx'b
    refine ⟨x', yb, hLx', hMyb, ?_⟩
    rw [spanOrLine_of_dist_eq_four hP hEY]
    rw [← hpx']
    exact hpS x' (by rw [Finset.mem_erase, mem_neighborFinset]; exact ⟨hx'b, hLx'⟩)

end LineCovering

end CFSG.Geometry.GeneralizedQuadrangles

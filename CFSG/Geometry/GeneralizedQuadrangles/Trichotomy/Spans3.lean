module

public import CFSG.Geometry.GeneralizedQuadrangles.Trichotomy.Spans

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section Basics

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem dist_eq_two_or_four_of_point_colors
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2)) {x y : V}
    (hx : c x = 0) (hy : c y = 0) (hne : x ≠ y) :
    Γ.dist x y = 2 ∨ Γ.dist x y = 4 := by
  have heven : Even (Γ.dist x y) :=
    (hP.eq_iff_even_dist c x y).1 (by rw [hx, hy])
  have hle : Γ.dist x y ≤ 4 := hP.dist_le (by norm_num) x y
  have hne0 : Γ.dist x y ≠ 0 := by
    intro h0
    exact hne ((hP.connected.dist_eq_zero_iff).mp h0)
  obtain ⟨k, hk⟩ := heven
  omega

end Basics

section BlockContainment

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem neighborSet_subset_spanUnion
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {L M x : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) : Γ.neighborSet M ⊆ spanUnion hP L M := by
  classical
  intro m hmM
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLx
  have hm0 : c m = 0 := color_eq_zero_of_adj_of_color_eq_one hM hmM
  have hxm_ne : x ≠ m := by
    rintro rfl
    have hLM2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := L) (y := M) (L := x)
        hLx hmM.symm (by rintro rfl; rw [SimpleGraph.dist_self] at hLM; omega)
    omega
  rcases dist_eq_two_or_four_of_point_colors hP c hx0 hm0 hxm_ne with h2 | h4
  · refine ⟨x, m, hLx, hmM, ?_⟩
    rw [spanOrLine_of_dist_eq_two hP h2]
    exact (commonNeighbor_adj_right hP h2).symm
  · refine ⟨x, m, hLx, hmM, ?_⟩
    rw [spanOrLine_of_dist_eq_four hP h4]
    exact right_mem_spanSet h4

theorem spanBlock_subset_spanUnion
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {p : ℕ}
    (hp : ∀ a b : V, c a = 0 → Γ.dist a b = 4 → (spanSet Γ a b).ncard = p + 1)
    {L M x T y z1 z2 : V}
    (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hxV : Γ.Adj x T) (hVy : Γ.Adj T y) (hMy : Γ.Adj M y)
    (hz1V : Γ.Adj T z1) (hz1y : z1 ≠ y) (hz2M : Γ.Adj M z2) (hz2y : z2 ≠ y)
    (hz1z2 : Γ.dist z1 z2 = 4) :
    spanBlock Γ y z1 z2 ⊆ spanUnion hP L M := by
  classical
  intro u hu
  unfold spanBlock at hu
  obtain ⟨W, hyW, hWT, hWu⟩ := hu
  obtain ⟨t, htT, hWt⟩ := hWT
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMy
  have hxy2 : Γ.dist x y = 2 := by
    refine dist_eq_two_of_adj_of_adj_of_ne hP (x := x) (y := y) (L := T) hxV hVy ?_
    intro hxy
    have hLM2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := L) (y := M) (L := y)
        (hxy ▸ hLx) hMy.symm (by rintro rfl; rw [SimpleGraph.dist_self] at hLM; omega)
    omega
  have hyz1 : Γ.dist y z1 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := z1) (L := T)
      hVy.symm hz1V hz1y.symm
  have hyz2 : Γ.dist y z2 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := z2) (L := M)
      hMy.symm hz2M hz2y.symm
  by_cases huM : u ∈ Γ.neighborSet M
  · exact neighborSet_subset_spanUnion hP c hL hM hLM hLx huM
  by_cases huV : u ∈ Γ.neighborSet T
  · have hVeq : T = commonNeighbor hP hxy2 :=
      (existsUnique_commonNeighbor hP hxy2).unique
        ⟨hxV, hVy.symm⟩ ⟨commonNeighbor_adj_left hP hxy2, commonNeighbor_adj_right hP hxy2⟩
    exact ⟨x, y, hLx, hMy, by
      rw [spanOrLine_of_dist_eq_two hP hxy2, ← hVeq]
      exact huV⟩
  by_cases hux2 : Γ.dist u x = 2
  · have huy2 : Γ.dist u y = 2 := by
      rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := u) (L := W)
        hyW hWu (by rintro rfl; exact huM hMy)
    obtain ⟨Vx, ⟨hux, hxu, hyu⟩, -⟩ :=
      existsUnique_commonNeighbor_of_pairwise_dist_two hP hux2 huy2 hxy2
    have hVeq : Vx = T :=
      (existsUnique_commonNeighbor hP hxy2).unique ⟨hxu, hyu⟩ ⟨hxV, hVy.symm⟩
    exfalso
    exact huV (hVeq ▸ hux).symm
  · have hu0 : c u = 0 := by
      have hW1 : c W = 1 := by
        have hne := c.valid hyW
        have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
        rcases hfin (c W) with h0 | h1
        · exact absurd (hy0.trans h0.symm) hne
        · exact h1
      exact color_eq_zero_of_adj_of_color_eq_one hW1 hWu
    have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLx
    have hux_ne : u ≠ x := by
      intro hEq
      subst hEq
      exact huV hxV.symm
    have hux4 : Γ.dist u x = 4 := by
      rcases dist_eq_two_or_four_of_point_colors hP c hu0 hx0 hux_ne with h2 | h4
      · exact absurd h2 hux2
      · exact h4
    have huy2 : Γ.dist u y = 2 := by
      rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := u) (L := W)
        hyW hWu (by rintro rfl; exact huM hMy)
    have hWV : W ≠ T := by
      intro hEq
      exact huV (hEq ▸ hWu)
    have hWmem : W ∈ linesThrough Γ y (spanSet Γ u x) ∩
        linesThrough Γ y (spanSet Γ z1 z2) := by
      constructor
      · rw [mem_linesThrough]
        exact ⟨hyW, u, left_mem_spanSet hux4, hWu⟩
      · rw [mem_linesThrough]
        exact ⟨hyW, t, htT, hWt⟩
    have hVmem : T ∈ linesThrough Γ y (spanSet Γ u x) ∩
        linesThrough Γ y (spanSet Γ z1 z2) := by
      constructor
      · rw [mem_linesThrough]
        exact ⟨hVy.symm, x, right_mem_spanSet hux4, hxV.symm⟩
      · rw [mem_linesThrough]
        exact ⟨hVy.symm, z1, left_mem_spanSet hz1z2, hz1V⟩
    have hlines : linesThrough Γ y (spanSet Γ u x) =
        linesThrough Γ y (spanSet Γ z1 z2) :=
      linesThrough_spanSet_eq_of_two_lines hP hT c hy0 (hH y hy0) hp
        (by rw [SimpleGraph.dist_comm]; exact huy2)
        (by rw [SimpleGraph.dist_comm]; exact hxy2) hyz1 hyz2 hux4 hz1z2
        hWmem hVmem hWV
    have hMmem : M ∈ linesThrough Γ y (spanSet Γ z1 z2) := by
      rw [mem_linesThrough]
      exact ⟨hMy.symm, z2, right_mem_spanSet hz1z2, hz2M⟩
    have hMlines : M ∈ linesThrough Γ y (spanSet Γ u x) := by
      rw [hlines]
      exact hMmem
    obtain ⟨m, hmS, hMm⟩ := hMlines.2
    have hmx_ne : m ≠ x := by
      intro hmx
      have hMx : Γ.Adj M x := hmx ▸ hMm
      have hLM2 : Γ.dist L M = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP (x := L) (y := M) (L := x)
          hLx hMx.symm (by rintro rfl; rw [SimpleGraph.dist_self] at hLM; omega)
      omega
    obtain ⟨hxm4, hspan, -⟩ :=
      span_eq_of_mem hP hT hux4 hmS (right_mem_spanSet hux4) hmx_ne
    have hu_xm : u ∈ spanSet Γ x m := by
      rw [spanSet_comm x m, hspan]
      exact left_mem_spanSet hux4
    refine ⟨x, m, hLx, hMm, ?_⟩
    rw [spanOrLine_of_dist_eq_four hP (by rw [SimpleGraph.dist_comm]; exact hxm4)]
    exact hu_xm

end BlockContainment

section Symmetry

variable {Γ : SimpleGraph V}

theorem spanOrLine_comm (hP : IsGeneralizedPolygon Γ 4) (x y : V) :
    spanOrLine hP x y = spanOrLine hP y x := by
  classical
  by_cases h4 : Γ.dist x y = 4
  · have h4' : Γ.dist y x = 4 := by rw [SimpleGraph.dist_comm]; exact h4
    rw [spanOrLine_of_dist_eq_four hP h4, spanOrLine_of_dist_eq_four hP h4',
      spanSet_comm]
  · by_cases h2 : Γ.dist x y = 2
    · have h2' : Γ.dist y x = 2 := by rw [SimpleGraph.dist_comm]; exact h2
      rw [spanOrLine_of_dist_eq_two hP h2, spanOrLine_of_dist_eq_two hP h2']
      have hEq : commonNeighbor hP h2 = commonNeighbor hP h2' :=
        (existsUnique_commonNeighbor hP h2).unique
          ⟨commonNeighbor_adj_left hP h2, commonNeighbor_adj_right hP h2⟩
          ⟨commonNeighbor_adj_right hP h2', commonNeighbor_adj_left hP h2'⟩
      rw [hEq]
    · have h4' : ¬ Γ.dist y x = 4 := fun h => h4 (by rwa [SimpleGraph.dist_comm] at h)
      have h2' : ¬ Γ.dist y x = 2 := fun h => h2 (by rwa [SimpleGraph.dist_comm] at h)
      rw [spanOrLine, spanOrLine, if_neg h4, dif_neg h2, if_neg h4', dif_neg h2']

theorem spanUnion_comm (hP : IsGeneralizedPolygon Γ 4) (L M : V) :
    spanUnion hP L M = spanUnion hP M L := by
  ext u
  constructor
  · rintro ⟨x, y, hLx, hMy, hu⟩
    refine ⟨y, x, hMy, hLx, ?_⟩
    rwa [spanOrLine_comm hP x y] at hu
  · rintro ⟨x, y, hMx, hLy, hu⟩
    refine ⟨y, x, hLy, hMx, ?_⟩
    rwa [spanOrLine_comm hP x y] at hu

end Symmetry

section Decomposition

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem exists_adj_ne_of_isThick
    (hT : IsThick Γ) {L x : V} (hxL : Γ.Adj L x) :
    ∃ z : V, Γ.Adj L z ∧ z ≠ x := by
  classical
  have h3 : 3 ≤ (Γ.neighborFinset L).card := by
    rw [card_neighborFinset_eq_degree]
    exact hT L
  have hmem : x ∈ Γ.neighborFinset L := by
    rw [mem_neighborFinset]
    exact hxL
  have herase : ((Γ.neighborFinset L).erase x).card = (Γ.neighborFinset L).card - 1 :=
    Finset.card_erase_of_mem hmem
  have hpos : 0 < ((Γ.neighborFinset L).erase x).card := by omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_erase, mem_neighborFinset] at hz
  exact ⟨z, hz.2, hz.1⟩

private theorem spanSet_subset_blockThrough_of_ne
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {ba : V} (hH : HasPropertyH Γ ba) {p : ℕ}
    (hp : ∀ a b : V, c a = 0 → Γ.dist a b = 4 → (spanSet Γ a b).ncard = p + 1)
    {L M a b x yb : V}
    (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLba : Γ.Adj L ba) (hLb : Γ.Adj L b) (hLx : Γ.Adj L x)
    (haL : ¬ Γ.Adj L a)
    (hba : Γ.dist ba a = 2) (hb : Γ.dist ba b = 2) (hyb : Γ.dist ba yb = 2)
    (hab : Γ.dist a b = 4) (hayb : Γ.dist a yb = 4)
    (hxS : x ∈ spanSet Γ a yb) :
    spanSet Γ a b ⊆ blockThrough Γ ba (spanSet Γ a yb) := by
  classical
  have hba0 : c ba = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLba
  have hba_mem : commonNeighbor hP hba ∈
      linesThrough Γ ba (spanSet Γ a b) ∩
      linesThrough Γ ba (spanSet Γ a yb) := by
    constructor
    · rw [mem_linesThrough]
      exact ⟨commonNeighbor_adj_left hP hba, a, left_mem_spanSet hab,
        (commonNeighbor_adj_right hP hba).symm⟩
    · rw [mem_linesThrough]
      exact ⟨commonNeighbor_adj_left hP hba, a, left_mem_spanSet hayb,
        (commonNeighbor_adj_right hP hba).symm⟩
  have hLmem : L ∈ linesThrough Γ ba (spanSet Γ a b) ∩
      linesThrough Γ ba (spanSet Γ a yb) := by
    constructor
    · rw [mem_linesThrough]
      exact ⟨hLba.symm, b, right_mem_spanSet hab, hLb⟩
    · rw [mem_linesThrough]
      exact ⟨hLba.symm, x, hxS, hLx⟩
  have hne : commonNeighbor hP hba ≠ L := by
    intro hEq
    exact haL (hEq ▸ (commonNeighbor_adj_right hP hba).symm)
  have hlines : linesThrough Γ ba (spanSet Γ a b) =
      linesThrough Γ ba (spanSet Γ a yb) :=
    linesThrough_spanSet_eq_of_two_lines hP hT c hba0 hH hp
      hba hb hba hyb hab hayb hba_mem hLmem hne
  intro u hu
  have htrace : ba ∈ traceSet Γ a b :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hba,
      by rw [SimpleGraph.dist_comm]; exact hb⟩
  have huba : Γ.dist u ba = 2 :=
    dist_eq_two_of_mem_span_of_mem_trace hP hT hab hu htrace
  let Ln : V := commonNeighbor hP huba
  have huba' : Γ.dist ba u = 2 := by rw [SimpleGraph.dist_comm]; exact huba
  let Ln' : V := commonNeighbor hP huba'
  have hLn' : Γ.Adj ba Ln' := commonNeighbor_adj_left hP huba'
  have hLn'u : Γ.Adj Ln' u := (commonNeighbor_adj_right hP huba').symm
  have hLn'mem : Ln' ∈ linesThrough Γ ba (spanSet Γ a b) := by
    rw [mem_linesThrough]
    exact ⟨hLn', u, hu, hLn'u⟩
  have hLn'mem' : Ln' ∈ linesThrough Γ ba (spanSet Γ a yb) := by
    rw [hlines] at hLn'mem
    exact hLn'mem
  exact ⟨Ln', hLn', hLn'mem'.2, hLn'u⟩

theorem spanOrLine_subset_blockThrough
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {ba : V} (hH : HasPropertyH Γ ba) {p : ℕ}
    (hp : ∀ a b : V, c a = 0 → Γ.dist a b = 4 → (spanSet Γ a b).ncard = p + 1)
    {L M a x yb : V}
    (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLba : Γ.Adj L ba) (hLx : Γ.Adj L x) (haL : ¬ Γ.Adj L a)
    (hba : Γ.dist ba a = 2) (hMyb : Γ.Adj M yb) (hbyb : Γ.dist ba yb = 2)
    (hayb : Γ.dist a yb = 4) (hxS : x ∈ spanSet Γ a yb) :
    ∀ b : V, Γ.Adj L b →
      spanOrLine hP a b ⊆ blockThrough Γ ba (spanSet Γ a yb) := by
  classical
  intro b hLb
  by_cases hb : b = ba
  · rw [hb]
    rw [spanOrLine_comm hP a ba, spanOrLine_of_dist_eq_two hP hba]
    exact neighborSet_subset_blockThrough (Γ := Γ) (y := ba) (T := spanSet Γ a yb)
      (W := commonNeighbor hP hba) (commonNeighbor_adj_left hP hba)
      ⟨a, left_mem_spanSet hayb, (commonNeighbor_adj_right hP hba).symm⟩
  · have hbb : Γ.dist ba b = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := ba) (y := b) (L := L)
        hLba.symm hLb (by rintro rfl; exact hb rfl)
    have hcnL : commonNeighbor hP hbb = L :=
      (existsUnique_commonNeighbor hP hbb).unique
        ⟨commonNeighbor_adj_left hP hbb, commonNeighbor_adj_right hP hbb⟩
        ⟨hLba.symm, hLb.symm⟩
    have hne : commonNeighbor hP hba ≠ L := by
      intro hEq
      exact haL (hEq ▸ (commonNeighbor_adj_right hP hba).symm)
    have hab : Γ.dist a b = 4 :=
      dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP hba hbb (by
        rw [hcnL]
        exact hne)
    rw [spanOrLine_of_dist_eq_four hP hab]
    exact spanSet_subset_blockThrough_of_ne hP hT c hH hp hL hM hLM hLba hLb hLx
      haL hba hbb hbyb hab hayb hxS

end Decomposition

end CFSG.Geometry.GeneralizedQuadrangles

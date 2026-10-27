module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Varieties

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section Helpers

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem exists_other_point (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {x : V} (hx : c x = 0) : ∃ y, c y = 0 ∧ y ≠ x := by
  classical
  have h3 : 0 < (Γ.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree, hdeg x, if_pos hx]
    have := hT x
    omega
  obtain ⟨L, hL⟩ := Finset.card_pos.mp h3
  rw [mem_neighborFinset] at hL
  obtain ⟨y, hxy, -⟩ := hP.exists_dist_eq hT hL 2 (by norm_num) (by norm_num)
  have hy : c y = 0 := by
    have h : c x = c y := (hP.eq_iff_even_dist c x y).2 (by rw [hxy]; norm_num)
    rw [← h]
    exact hx
  refine ⟨y, hy, ?_⟩
  intro h
  rw [h] at hxy
  simp at hxy

private theorem exists_mem_span_of_line_through_trace (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {x y m M : V}
    (hxy : Γ.dist x y = 4) (hm : m ∈ traceSet Γ x y) (hm0 : c m = 0) (hM : c M = 1)
    (hmM : Γ.Adj M m) : ∃ w ∈ spanSet Γ x y, Γ.Adj M w := by
  classical
  have hxm : Γ.dist x m = 2 := hm.1
  have hym : Γ.dist y m = 2 := hm.2
  have hx0 : c x = 0 := by
    have h : c m = c x :=
      (hP.eq_iff_even_dist c m x).2 (by rw [SimpleGraph.dist_comm, hxm]; norm_num)
    rw [← h]
    exact hm0
  have hy0 : c y = 0 := by
    have h : c m = c y :=
      (hP.eq_iff_even_dist c m y).2 (by rw [SimpleGraph.dist_comm, hym]; norm_num)
    rw [← h]
    exact hm0
  have hTcard : (spanSet Γ x y).ncard = t + 1 := by
    rw [hreg x hx0 y hxy, hdeg x, if_pos hx0]
  let f : ↥(spanSet Γ x y) → V := fun w =>
    commonNeighbor hP (dist_eq_two_of_mem_span_of_mem_trace hP hT hxy w.2 hm)
  have hfmem : ∀ w : ↥(spanSet Γ x y), f w ∈ Γ.neighborSet m := fun w =>
    commonNeighbor_adj_right hP
      (dist_eq_two_of_mem_span_of_mem_trace hP hT hxy w.2 hm)
  have hfinj : Function.Injective f := by
    intro w w' hww'
    apply Subtype.ext
    by_contra hne
    have h4 : Γ.dist w.1 w'.1 = 4 :=
      dist_eq_four_of_mem_span hP hT hxy w.2 w'.2 hne
    have hw : Γ.Adj w.1 (f w) :=
      commonNeighbor_adj_left hP
        (dist_eq_two_of_mem_span_of_mem_trace hP hT hxy w.2 hm)
    have hw' : Γ.Adj (f w) w'.1 := by
      have h : Γ.Adj w'.1 (f w') :=
        commonNeighbor_adj_left hP
          (dist_eq_two_of_mem_span_of_mem_trace hP hT hxy w'.2 hm)
      rw [← hww'] at h
      exact h.symm
    have h2 : Γ.dist w.1 w'.1 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hw hw' hne
    omega
  have himg : (Set.range f).ncard = (spanSet Γ x y).ncard := by
    rw [Set.ncard_range_of_injective hfinj, Nat.card_coe_set_eq]
  have hsub : Set.range f ⊆ Γ.neighborSet m := by
    rintro z ⟨w, rfl⟩
    exact hfmem w
  have hNcard : (Γ.neighborSet m).ncard = t + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg m, if_pos hm0]
  have hrange : Set.range f = Γ.neighborSet m := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [hNcard, himg, hTcard]
  have hMmem : M ∈ Γ.neighborSet m := hmM.symm
  obtain ⟨w, hwM⟩ := hrange ▸ hMmem
  refine ⟨w.1, w.2, ?_⟩
  rw [← hwM]
  exact (commonNeighbor_adj_left hP
    (dist_eq_two_of_mem_span_of_mem_trace hP hT hxy w.2 hm)).symm

private theorem isStarCollinear_self_left (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {a b : V} (ha : c a = 0) (hb : c b = 0) (hab : a ≠ b) :
    IsStarCollinear Γ c a a b :=
  ⟨starLine Γ c a b, isStarLine_starLine ha hb hab, mem_starLine_left ha,
    mem_starLine_left ha, mem_starLine_right hb⟩

private theorem isStarCollinear_mid (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {a b : V} (ha : c a = 0) (hb : c b = 0) (hab : a ≠ b) :
    IsStarCollinear Γ c a b a :=
  ⟨starLine Γ c a b, isStarLine_starLine ha hb hab, mem_starLine_left ha,
    mem_starLine_right hb, mem_starLine_left ha⟩

private theorem isStarCollinear_self_right (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {a b : V} (ha : c a = 0) (hb : c b = 0) (hab : a ≠ b) :
    IsStarCollinear Γ c a b b :=
  ⟨starLine Γ c a b, isStarLine_starLine ha hb hab, mem_starLine_left ha,
    mem_starLine_right hb, mem_starLine_right hb⟩

private theorem isStarCollinear_self_all (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {a : V} (ha : c a = 0) :
    IsStarCollinear Γ c a a a := by
  obtain ⟨b, hb, hba⟩ := exists_other_point hP hT c hdeg ha
  exact ⟨starLine Γ c a b, isStarLine_starLine ha hb (Ne.symm hba), mem_starLine_left ha,
    mem_starLine_left ha, mem_starLine_left ha⟩

private theorem ncard_le_of_isLinearVariety_pairwise_opposite (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V}
    (hX : IsLinearVariety Γ c X)
    (hpair : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Γ.dist x y = 4)
    (h3 : ∃ x ∈ X, ∃ y ∈ X, ∃ z ∈ X, ¬ IsStarCollinear Γ c x y z) :
    t ^ 2 + t + 1 ≤ X.ncard := by
  classical
  obtain ⟨x, hxX, y, hyX, z, hzX, hnc⟩ := h3
  have hx0 : c x = 0 := hX.1 x hxX
  have hy0 : c y = 0 := hX.1 y hyX
  have hz0 : c z = 0 := hX.1 z hzX
  have hxy : x ≠ y := by
    intro h
    subst y
    by_cases hxz : x = z
    · subst z
      exact hnc (isStarCollinear_self_all hP hT c hdeg hx0)
    · exact hnc (isStarCollinear_self_left hP hT c hx0 hz0 hxz)
  have hxz : x ≠ z := by
    intro h
    subst z
    exact hnc (isStarCollinear_mid hP hT c hx0 hy0 hxy)
  have hyz : y ≠ z := by
    intro h
    subst z
    exact hnc (isStarCollinear_self_right hP hT c hx0 hy0 hxy)
  let S : Set V := starLine Γ c y z
  have hSsubX : S ⊆ X := by
    intro w hw
    change w ∈ starLine Γ c y z at hw
    exact hX.2 y hyX z hzX hyz hw
  have hScard : S.ncard = t + 1 := by
    have hyz4 : Γ.dist y z = 4 := hpair y hyX z hzX hyz
    change (starLine Γ c y z).ncard = t + 1
    exact ncard_starLine_of_dist_four hP hT c hdeg hreg hy0 hyz4
  have hx_notS : x ∉ S := by
    intro hxS
    apply hnc
    exact ⟨S, isStarLine_starLine hy0 hz0 hyz, hxS, mem_starLine_left hy0,
      mem_starLine_right hz0⟩
  let Sf : Finset V := S.toFinset
  have hSfcard : Sf.card = t + 1 := by
    change S.toFinset.card = t + 1
    rw [← Set.ncard_eq_toFinset_card' S, hScard]
  let T : V → Finset V := fun w => ((starLine Γ c x w).toFinset).erase x
  have hTcard : ∀ w ∈ Sf, (T w).card = t := by
    intro w hwSf
    have hwS : w ∈ S := by simpa [Sf] using hwSf
    have hwX : w ∈ X := hSsubX hwS
    have hw0 : c w = 0 := hX.1 w hwX
    have hxw : x ≠ w := by
      intro h
      exact hx_notS (by rw [h]; exact hwS)
    have hxw4 : Γ.dist x w = 4 := hpair x hxX w hwX hxw
    have hstar : (starLine Γ c x w).ncard = t + 1 :=
      ncard_starLine_of_dist_four hP hT c hdeg hreg hx0 hxw4
    have hto : ((starLine Γ c x w).toFinset).card = t + 1 := by
      rw [← Set.ncard_eq_toFinset_card' (starLine Γ c x w), hstar]
    change (((starLine Γ c x w).toFinset).erase x).card = t
    rw [Finset.card_erase_of_mem (by simpa using mem_starLine_left hx0), hto]
    omega
  have hdisj : (Sf : Set V).PairwiseDisjoint T := by
    intro w hwSf w' hw'Sf hww'
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    have hwS : w ∈ S := by simpa [Sf] using hwSf
    have hw'S : w' ∈ S := by simpa [Sf] using hw'Sf
    have hwX : w ∈ X := hSsubX hwS
    have hw'X : w' ∈ X := hSsubX hw'S
    have hw0 : c w = 0 := hX.1 w hwX
    have hw'0 : c w' = 0 := hX.1 w' hw'X
    have hxw : x ≠ w := by
      intro h
      exact hx_notS (by rw [h]; exact hwS)
    have hxw' : x ≠ w' := by
      intro h
      exact hx_notS (by rw [h]; exact hw'S)
    have huT : u ∈ ((starLine Γ c x w).toFinset).erase x := by
      simpa only [T] using hu
    have huT' : u ∈ ((starLine Γ c x w').toFinset).erase x := by
      simpa only [T] using hu'
    rw [Finset.mem_erase] at huT huT'
    have hu_star : u ∈ starLine Γ c x w := by simpa using huT.2
    have hu_star' : u ∈ starLine Γ c x w' := by simpa using huT'.2
    have hu0 : c u = 0 := color_eq_zero_of_mem_starLine hu_star
    have hxu : x ≠ u := fun h => huT.1 h.symm
    have heq1 : starLine Γ c x u = starLine Γ c x w :=
      starLine_eq_of_mem hP hT c hx0 hw0 hxw (mem_starLine_left hx0) hu_star hxu
    have heq2 : starLine Γ c x u = starLine Γ c x w' :=
      starLine_eq_of_mem hP hT c hx0 hw'0 hxw' (mem_starLine_left hx0) hu_star' hxu
    have heq : starLine Γ c x w = starLine Γ c x w' := heq1.symm.trans heq2
    have hw_in : w ∈ starLine Γ c x w' := by
      rw [← heq]
      exact mem_starLine_right hw0
    have hw'_in : w' ∈ starLine Γ c x w := by
      rw [heq]
      exact mem_starLine_right hw'0
    have hTw : starLine Γ c w w' = starLine Γ c x w :=
      starLine_eq_of_mem hP hT c hx0 hw0 hxw (mem_starLine_right hw0) hw'_in hww'
    have hSw : starLine Γ c w w' = S := by
      change starLine Γ c w w' = starLine Γ c y z
      exact starLine_eq_of_mem hP hT c hy0 hz0 hyz hwS hw'S hww'
    have hSx : S = starLine Γ c x w := hSw.symm.trans hTw
    exact hx_notS (by rw [hSx]; exact mem_starLine_left hx0)
  let U : Finset V := insert x (Sf.biUnion T)
  have hx_not_union : x ∉ Sf.biUnion T := by
    intro hxmem
    rw [Finset.mem_biUnion] at hxmem
    obtain ⟨w, -, hxT⟩ := hxmem
    have hxT' : x ∈ ((starLine Γ c x w).toFinset).erase x := by
      simpa only [T] using hxT
    rw [Finset.mem_erase] at hxT'
    exact hxT'.1 rfl
  have hUcard : U.card = 1 + (t + 1) * t := by
    rw [Finset.card_insert_of_notMem hx_not_union]
    rw [Finset.card_biUnion hdisj]
    have hsum : ∑ w ∈ Sf, (T w).card = Sf.card * t := by
      calc
        ∑ w ∈ Sf, (T w).card = ∑ w ∈ Sf, t :=
          Finset.sum_congr rfl fun w hw => hTcard w hw
        _ = Sf.card * t := by rw [Finset.sum_const, smul_eq_mul]
    rw [hsum, hSfcard]
    ring
  have hUsubX : (U : Set V) ⊆ X := by
    intro u hu
    rw [Finset.mem_coe, Finset.mem_insert] at hu
    rcases hu with rfl | hu
    · exact hxX
    · rw [Finset.mem_biUnion] at hu
      obtain ⟨w, hwSf, huT⟩ := hu
      have hwS : w ∈ S := by simpa [Sf] using hwSf
      have hwX : w ∈ X := hSsubX hwS
      have hw0 : c w = 0 := hX.1 w hwX
      have hxw : x ≠ w := by
        intro h
        exact hx_notS (by rw [h]; exact hwS)
      have hu_star : u ∈ starLine Γ c x w := by
        rw [Finset.mem_erase] at huT
        simpa using huT.2
      exact hX.2 x hxX w hwX hxw hu_star
  have hUle : U.card ≤ X.ncard := by
    have h := Set.ncard_le_ncard (s := (U : Set V)) (t := X) hUsubX
    simpa using h
  calc
    t ^ 2 + t + 1 = 1 + (t + 1) * t := by ring
    _ = U.card := hUcard.symm
    _ ≤ X.ncard := hUle

private theorem ncard_le_s_add_one_of_misses_line (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V}
    (hX : IsLinearVariety Γ c X)
    (hpair : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Γ.dist x y = 4) {M : V} (hM : c M = 1)
    (hmiss : ∀ x ∈ X, ¬ Γ.Adj M x) : X.ncard ≤ s + 1 := by
  classical
  have hxoff : ∀ x : X, ¬ Γ.Adj M x.1 := fun x => hmiss x.1 x.2
  have hdist3 : ∀ x : X, Γ.dist x.1 M = 3 := fun x =>
    dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hxoff x h.symm)
      (by rw [hX.1 x.1 x.2, hM]; norm_num)
  let f : X → V := fun x => proj hP (hdist3 x)
  have hfmem : ∀ x : X, Γ.Adj M (f x) := fun x => proj_adj hP (hdist3 x)
  have hfdist : ∀ x : X, Γ.dist x.1 (f x) = 2 := fun x => proj_dist hP (hdist3 x)
  have hinj : Function.Injective f := by
    intro x x' hxx'
    apply Subtype.ext
    by_contra hne
    have h4 : Γ.dist x.1 x'.1 = 4 := hpair x.1 x.2 x'.1 x'.2 hne
    have hm0 : c (f x) = 0 := color_eq_zero_of_adj_of_color_eq_one hM (hfmem x)
    have hxf' : Γ.dist x'.1 (f x) = 2 := by
      rw [hxx']
      exact hfdist x'
    have hm_trace : f x ∈ traceSet Γ x.1 x'.1 := ⟨hfdist x, hxf'⟩
    obtain ⟨w, hwSpan, hMw⟩ :=
      exists_mem_span_of_line_through_trace hP hT c hdeg hreg h4 hm_trace hm0 hM (hfmem x)
    have hspan_sub : spanSet Γ x.1 x'.1 ⊆ X := by
      intro z hz
      exact hX.2 x.1 x.2 x'.1 x'.2 hne (by
        rw [starLine_eq_spanSet hP hT c (hX.1 x.1 x.2) h4]
        exact hz)
    exact hmiss w (hspan_sub hwSpan) hMw
  have himg : (Set.range f).ncard = X.ncard := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_coe_set_eq]
  have hsub : Set.range f ⊆ Γ.neighborSet M := by
    rintro z ⟨x, rfl⟩
    exact hfmem x
  have hNcard : (Γ.neighborSet M).ncard = s + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg M, if_neg (by rw [hM]; decide)]
  calc
    X.ncard = (Set.range f).ncard := himg.symm
    _ ≤ (Γ.neighborSet M).ncard := Set.ncard_le_ncard hsub
    _ = s + 1 := hNcard

theorem isOvoid_of_isLinearVariety (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsLinearVariety Γ c X)
    (hpair : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Γ.dist x y = 4)
    (h3 : ∃ x ∈ X, ∃ y ∈ X, ∃ z ∈ X, ¬ IsStarCollinear Γ c x y z) : IsOvoid Γ c X := by
  refine ⟨hX.1, ?_⟩
  intro M hM
  have hmeet : ∃ x ∈ X, Γ.Adj M x := by
    by_contra hmiss
    have hmiss' : ∀ x ∈ X, ¬ Γ.Adj M x := fun x hx h => hmiss ⟨x, hx, h⟩
    have hupper := ncard_le_s_add_one_of_misses_line hP hT c hdeg hreg hX hpair hM hmiss'
    have hlower :=
      ncard_le_of_isLinearVariety_pairwise_opposite hP hT c hdeg hreg hX hpair h3
    have ht : 2 ≤ t := two_le_t hP hT c hdeg
    have hs : s ≤ t ^ 2 := higman_s_le_t_sq hP hT c hdeg
    omega
  obtain ⟨x, hxX, hMx⟩ := hmeet
  have hsingle : Γ.neighborSet M ∩ X = {x} := by
    ext y
    constructor
    · rintro ⟨hyM, hyX⟩
      by_contra hyx
      have hy4 : Γ.dist y x = 4 := hpair y hyX x hxX hyx
      have h2 : Γ.dist y x = 2 := dist_eq_two_of_adj_of_adj_of_ne hP hyM.symm hMx hyx
      omega
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨hMx, hxX⟩
  rw [hsingle]
  simp

theorem isStarPlane_cases (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsStarPlane Γ c X) :
    IsAbsPlane Γ c X ∨ IsNonabsPlane Γ c X := by
  classical
  have hlin : IsLinearVariety Γ c X := hX.1.1
  by_cases hcol : ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ Γ.dist x y = 2
  · left
    obtain ⟨x, hxX, y, hyX, hxy, hxy2⟩ := hcol
    let L : V := commonNeighbor hP hxy2
    have hL : c L = 1 :=
      color_eq_one_of_adj_of_color_eq_zero (hlin.1 x hxX) (commonNeighbor_adj_left hP hxy2)
    have hLX : Γ.neighborSet L ⊆ X := by
      intro w hw
      exact hlin.2 x hxX y hyX hxy (by
        rw [starLine_eq_neighborSet hP hT c (hlin.1 x hxX) hxy2]
        exact hw)
    have hz_exists : ∃ z ∈ X, ¬ Γ.Adj L z := by
      by_contra h
      push Not at h
      obtain ⟨a, haX, b, hbX, d, hdX, hnc⟩ := hX.2
      apply hnc
      refine ⟨starLine Γ c x y,
        isStarLine_starLine (hlin.1 x hxX) (hlin.1 y hyX) hxy, ?_, ?_, ?_⟩
      · rw [starLine_eq_neighborSet hP hT c (hlin.1 x hxX) hxy2]
        exact h a haX
      · rw [starLine_eq_neighborSet hP hT c (hlin.1 x hxX) hxy2]
        exact h b hbX
      · rw [starLine_eq_neighborSet hP hT c (hlin.1 x hxX) hxy2]
        exact h d hdX
    obtain ⟨z, hzX, hzL⟩ := hz_exists
    have hz0 : c z = 0 := hlin.1 z hzX
    obtain ⟨u, ⟨huL, hzu⟩, -⟩ :=
      existsUnique_proj_of_not_adj hP hz0 hL (fun h => hzL h.symm)
    refine ⟨u, ?_, ?_⟩
    · exact color_eq_zero_of_dist_eq_two hP hz0 hzu
    · exact eq_ptPerp_of_isProperVariety hP hT c hdeg hreg hX.1 hL hLX hzX hzL huL hzu
  · right
    refine ⟨hX, isOvoid_of_isLinearVariety hP hT c hdeg hreg hlin ?_ hX.2⟩
    intro x hx y hy hxy
    rcases dist_eq_two_or_four_of_color_zero hP (hlin.1 x hx) (hlin.1 y hy) hxy with h2 | h4
    · exact absurd ⟨x, hx, y, hy, hxy, h2⟩ hcol
    · exact h4

private theorem not_isOvoid_subset_isAbsPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {X Y : Set V} (hX : IsAbsPlane Γ c X) (hY : IsOvoid Γ c Y) (hsub : Y ⊆ X) : False := by
  classical
  obtain ⟨u, hu, rfl⟩ := hX
  have hYcard : Y.ncard = s * t + 1 := ncard_of_isOvoid hP hT c hdeg hY
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have hu_notY : u ∉ Y := by
    intro huY
    have hY2 : 1 < Y.ncard := by
      rw [hYcard]
      nlinarith
    obtain ⟨y, hyY, hyu⟩ := Set.exists_ne_of_one_lt_ncard hY2 u
    have hy_sub := hsub hyY
    have hy0 : c y = 0 := hy_sub.1
    have hle : Γ.dist y u ≤ 2 := hy_sub.2 u (Set.mem_singleton u)
    have hyu' : Γ.dist y u = 2 :=
      dist_eq_two_of_le_two_of_ne hP hy0 hu hyu hle
    let L : V := commonNeighbor hP hyu'
    have hL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 (commonNeighbor_adj_left hP hyu')
    have hyL : Γ.Adj L y := (commonNeighbor_adj_left hP hyu').symm
    have huL : Γ.Adj L u := (commonNeighbor_adj_right hP hyu').symm
    have h1 := hY.2 L hL
    have hlt : 1 < (Γ.neighborSet L ∩ Y).ncard :=
      (Set.one_lt_ncard).mpr ⟨u, ⟨huL, huY⟩, y, ⟨hyL, hyY⟩, Ne.symm hyu⟩
    omega
  have hy_dist : ∀ y ∈ Y, Γ.dist y u = 2 := by
    intro y hyY
    have hy_sub := hsub hyY
    have hy0 : c y = 0 := hy_sub.1
    have hle : Γ.dist y u ≤ 2 := hy_sub.2 u (Set.mem_singleton u)
    exact dist_eq_two_of_le_two_of_ne hP hy0 hu (fun h => hu_notY (h ▸ hyY)) hle
  let f : Y → V := fun y => commonNeighbor hP (hy_dist y.1 y.2)
  have hfinj : Function.Injective f := by
    intro y y' hyy'
    apply Subtype.ext
    by_contra hne
    have hy0 : c y.1 = 0 := (hsub y.2).1
    let L : V := f y
    have hL : c L = 1 :=
      color_eq_one_of_adj_of_color_eq_zero hy0
        (commonNeighbor_adj_left hP (hy_dist y.1 y.2))
    have hyL : Γ.Adj L y.1 := (commonNeighbor_adj_left hP (hy_dist y.1 y.2)).symm
    have hy'L : Γ.Adj L y'.1 := by
      have h : Γ.Adj y'.1 (f y') := commonNeighbor_adj_left hP (hy_dist y'.1 y'.2)
      rw [← hyy'] at h
      exact h.symm
    have hmem : y.1 ∈ Γ.neighborSet L ∩ Y := ⟨hyL, y.2⟩
    have hmem' : y'.1 ∈ Γ.neighborSet L ∩ Y := ⟨hy'L, y'.2⟩
    obtain ⟨a, ha⟩ := (Set.ncard_eq_one).mp (hY.2 L hL)
    have hya : y.1 = a := by
      have h : y.1 ∈ ({a} : Set V) := by rw [← ha]; exact hmem
      simpa using h
    have hy'a : y'.1 = a := by
      have h : y'.1 ∈ ({a} : Set V) := by rw [← ha]; exact hmem'
      simpa using h
    exact hne (hya.trans hy'a.symm)
  have himg : (Set.range f).ncard = Y.ncard := by
    rw [Set.ncard_range_of_injective hfinj, Nat.card_coe_set_eq]
  have hsubN : Set.range f ⊆ Γ.neighborSet u := by
    rintro z ⟨y, rfl⟩
    exact commonNeighbor_adj_right hP (hy_dist y.1 y.2)
  have hNcard : (Γ.neighborSet u).ncard = t + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg u, if_pos hu]
  have hle : Y.ncard ≤ t + 1 := by
    calc
      Y.ncard = (Set.range f).ncard := himg.symm
      _ ≤ (Γ.neighborSet u).ncard := Set.ncard_le_ncard hsubN
      _ = t + 1 := hNcard
  nlinarith

private theorem ncard_of_isAbsPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {X : Set V} (hX : IsAbsPlane Γ c X) : X.ncard = s * t + s + 1 := by
  obtain ⟨u, hu, rfl⟩ := hX
  exact ncard_ptPerp_singleton hP hT c hdeg hu

private theorem ncard_of_isNonabsPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {X : Set V} (hX : IsNonabsPlane Γ c X) : X.ncard = s * t + 1 :=
  ncard_of_isOvoid hP hT c hdeg hX.2

theorem eq_of_isStarPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X Y : Set V} (hX : IsStarPlane Γ c X)
    (hY : IsStarPlane Γ c Y) {x y z : V} (hx : x ∈ X ∩ Y) (hy : y ∈ X ∩ Y)
    (hz : z ∈ X ∩ Y) (hxyz : ¬ IsStarCollinear Γ c x y z) : X = Y := by
  classical
  by_cases hXY : X = Y
  · exact hXY
  have hIlin : IsLinearVariety Γ c (X ∩ Y) := by
    refine ⟨?_, ?_⟩
    · intro a ha
      exact hX.1.1.1 a ha.1
    · intro a ha b hb hab w hw
      exact ⟨hX.1.1.2 a ha.1 b hb.1 hab hw, hY.1.1.2 a ha.2 b hb.2 hab hw⟩
  have hIproper : IsProperVariety Γ c (X ∩ Y) := by
    refine ⟨hIlin, ?_⟩
    obtain ⟨w, hw0, hwX⟩ := hX.1.2
    exact ⟨w, hw0, fun hw => hwX hw.1⟩
  have hI : IsStarPlane Γ c (X ∩ Y) :=
    ⟨hIproper, x, hx, y, hy, z, hz, hxyz⟩
  have hXcases := isStarPlane_cases hP hT c hdeg hreg hX
  have hYcases := isStarPlane_cases hP hT c hdeg hreg hY
  have hIcases := isStarPlane_cases hP hT c hdeg hreg hI
  rcases hIcases with hIabs | hInon
  · have hIcard : (X ∩ Y).ncard = s * t + s + 1 :=
      ncard_of_isAbsPlane hP hT c hdeg hIabs
    rcases hXcases with hXabs | hXnon
    · have hXcard : X.ncard = s * t + s + 1 := ncard_of_isAbsPlane hP hT c hdeg hXabs
      have hIX : X ∩ Y = X :=
        Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by rw [hXcard, hIcard])
      rcases hYcases with hYabs | hYnon
      · have hYcard : Y.ncard = s * t + s + 1 := ncard_of_isAbsPlane hP hT c hdeg hYabs
        have hIY : X ∩ Y = Y :=
          Set.eq_of_subset_of_ncard_le Set.inter_subset_right (by rw [hYcard, hIcard])
        exact absurd (hIX.symm.trans hIY) hXY
      · have hYcard : Y.ncard = s * t + 1 := ncard_of_isNonabsPlane hP hT c hdeg hYnon
        have hle : (X ∩ Y).ncard ≤ Y.ncard := Set.ncard_le_ncard Set.inter_subset_right
        have hs : 2 ≤ s := two_le_s hP hT c hdeg
        omega
    · have hXcard : X.ncard = s * t + 1 := ncard_of_isNonabsPlane hP hT c hdeg hXnon
      have hle : (X ∩ Y).ncard ≤ X.ncard := Set.ncard_le_ncard Set.inter_subset_left
      have hs : 2 ≤ s := two_le_s hP hT c hdeg
      omega
  · have hIcard : (X ∩ Y).ncard = s * t + 1 :=
      ncard_of_isNonabsPlane hP hT c hdeg hInon
    rcases hXcases with hXabs | hXnon
    · exact (not_isOvoid_subset_isAbsPlane hP hT c hdeg hXabs hInon.2
        Set.inter_subset_left).elim
    · have hXcard : X.ncard = s * t + 1 := ncard_of_isNonabsPlane hP hT c hdeg hXnon
      have hIX : X ∩ Y = X :=
        Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by rw [hXcard, hIcard])
      rcases hYcases with hYabs | hYnon
      · exact (not_isOvoid_subset_isAbsPlane hP hT c hdeg hYabs hInon.2
          Set.inter_subset_right).elim
      · have hYcard : Y.ncard = s * t + 1 := ncard_of_isNonabsPlane hP hT c hdeg hYnon
        have hIY : X ∩ Y = Y :=
          Set.eq_of_subset_of_ncard_le Set.inter_subset_right (by rw [hYcard, hIcard])
        exact absurd (hIX.symm.trans hIY) hXY

theorem talliniCondPrime_of_talliniCond (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (h : TalliniCond Γ c) :
    TalliniCondPrime Γ c := by
  classical
  intro x y z hx0 hy0 hz0 hxyz
  have hxy : x ≠ y := by
    intro hxy
    subst y
    by_cases hxz : x = z
    · subst z
      exact hxyz (isStarCollinear_self_all hP hT c hdeg hx0)
    · exact hxyz (isStarCollinear_self_left hP hT c hx0 hz0 hxz)
  have hxz : x ≠ z := by
    intro hxz
    subst z
    exact hxyz (isStarCollinear_mid hP hT c hx0 hy0 hxy)
  let L : Set V := starLine Γ c x y
  let L' : Set V := starLine Γ c x z
  have hL : IsStarLine Γ c L := isStarLine_starLine hx0 hy0 hxy
  have hL' : IsStarLine Γ c L' := isStarLine_starLine hx0 hz0 hxz
  have hLdual := ptPerp_ptPerp_starLine hP hT c hdeg hreg hL
  have hL'dual := ptPerp_ptPerp_starLine hP hT c hdeg hreg hL'
  have hLsub : ptPerp Γ c L ⊆ ptPerp Γ c {x} := by
    intro w hw
    rw [mem_ptPerp] at hw ⊢
    refine ⟨hw.1, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hw.2 x (mem_starLine_left hx0)
  have hL'sub : ptPerp Γ c L' ⊆ ptPerp Γ c {x} := by
    intro w hw
    rw [mem_ptPerp] at hw ⊢
    refine ⟨hw.1, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hw.2 x (mem_starLine_left hx0)
  have hproper : IsProperVariety Γ c (ptPerp Γ c {x}) :=
    (isStarPlane_ptPerp_singleton hP hT c hdeg hx0).1
  obtain ⟨W, hW, hWsub⟩ :=
    h (ptPerp Γ c L) (ptPerp Γ c L') hLdual.1 hL'dual.1
      ⟨ptPerp Γ c {x}, hproper, Set.union_subset hLsub hL'sub⟩
  have hLW : L ⊆ W := by
    intro a ha
    have ha' : a ∈ ptPerp Γ c (ptPerp Γ c L) := by
      rw [hLdual.2]
      exact ha
    exact hWsub (Set.mem_union_left _ ha')
  have hL'W : L' ⊆ W := by
    intro a ha
    have ha' : a ∈ ptPerp Γ c (ptPerp Γ c L') := by
      rw [hL'dual.2]
      exact ha
    exact hWsub (Set.mem_union_right _ ha')
  have hxW : x ∈ W := hLW (mem_starLine_left hx0)
  have hyW : y ∈ W := hLW (mem_starLine_right hy0)
  have hzW : z ∈ W := hL'W (mem_starLine_right hz0)
  refine ⟨W, ?_, hxW, hyW, hzW⟩
  exact ⟨hW, x, hxW, y, hyW, z, hzW, hxyz⟩

private theorem exists_line_missing_hypLine (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ) :
    ∃ M, c M = 1 ∧ ∀ w ∈ ℓ, ¬ Γ.Adj M w := by
  classical
  obtain ⟨x, y, hx, hdist, hℓeq⟩ := hℓ
  rw [hℓeq]
  have hcard : (starLine Γ c x y).ncard = t + 1 :=
    ncard_starLine_of_dist_four hP hT c hdeg hreg hx hdist
  have h0 : ∀ w ∈ starLine Γ c x y, c w = 0 := fun w hw =>
    color_eq_zero_of_mem_starLine hw
  have hdegw : ∀ w ∈ starLine Γ c x y, (Γ.neighborFinset w).card = t + 1 := by
    intro w hw
    rw [card_neighborFinset_eq_degree, hdeg w, if_pos (h0 w hw)]
  let U : Finset V := (starLine Γ c x y).toFinset.biUnion (fun w => Γ.neighborFinset w)
  have hUcard : U.card ≤ (starLine Γ c x y).toFinset.card * (t + 1) := by
    refine Finset.card_biUnion_le_card_mul _ _ _ ?_
    intro w hw
    exact le_of_eq (hdegw w (by simpa using hw))
  have hUt : (starLine Γ c x y).toFinset.card = t + 1 := by
    rw [← Set.ncard_eq_toFinset_card' (starLine Γ c x y), hcard]
  have hU : U.card ≤ (t + 1) * (t + 1) := by
    rw [hUt] at hUcard
    exact hUcard
  let Meet : Finset V := (lineFinset c).filter (fun M => ∃ w ∈ starLine Γ c x y, Γ.Adj M w)
  have hMeet_sub : Meet ⊆ U := by
    intro M hM
    rw [Finset.mem_filter] at hM
    obtain ⟨hMline, w, hw, hMw⟩ := hM
    change M ∈ (starLine Γ c x y).toFinset.biUnion (fun w => Γ.neighborFinset w)
    rw [Finset.mem_biUnion]
    refine ⟨w, by simpa using hw, ?_⟩
    rw [mem_neighborFinset]
    exact hMw.symm
  have hMeet_le : Meet.card ≤ (t + 1) * (t + 1) :=
    (Finset.card_le_card hMeet_sub).trans hU
  have hline : (lineFinset c).card = (t + 1) * (s * t + 1) :=
    card_lineFinset hP hT c hdeg
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have hlt : (t + 1) * (t + 1) < (lineFinset c).card := by
    rw [hline]
    refine Nat.mul_lt_mul_of_pos_left ?_ (by omega : 0 < t + 1)
    nlinarith
  have hMeet_lt : Meet.card < (lineFinset c).card := lt_of_le_of_lt hMeet_le hlt
  obtain ⟨M, hMline, hMnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hMeet_lt
  refine ⟨M, mem_lineFinset.mp hMline, ?_⟩
  intro w hw hMw
  apply hMnot
  change M ∈ (lineFinset c).filter (fun M => ∃ w ∈ starLine Γ c x y, Γ.Adj M w)
  rw [Finset.mem_filter]
  exact ⟨hMline, w, hw, hMw⟩

private theorem existsUnique_starPlane_of_hypLine_and_point (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c)
    {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ) {m : V} (hm : c m = 0) (hmℓ : m ∉ ℓ) :
    ∃! X, IsStarPlane Γ c X ∧ ℓ ⊆ X ∧ m ∈ X := by
  classical
  obtain ⟨x, y, hx, hxy4, hℓeq⟩ := hℓ
  rw [hℓeq] at hmℓ ⊢
  have hy0 : c y = 0 := by
    have h : c x = c y := (hP.eq_iff_even_dist c x y).2 (by
      rw [hxy4]
      exact ⟨2, by norm_num⟩)
    rw [← h]
    exact hx
  have hxy : x ≠ y := by
    rintro rfl
    simp at hxy4
  have hnc : ¬ IsStarCollinear Γ c x y m := by
    rintro ⟨X, hX, hxX, hyX, hmX⟩
    have hXeq : X = starLine Γ c x y :=
      starLine_eq_of_isStarLine_of_mem hP hT hX hxX hyX hxy
    exact hmℓ (by rwa [hXeq] at hmX)
  obtain ⟨X, hXplane, hxX, hyX, hmX⟩ := hii x y m hx hy0 hm hnc
  refine ⟨X, ⟨hXplane, ?_, hmX⟩, ?_⟩
  · exact hXplane.1.1.2 x hxX y hyX hxy
  · intro Y hY
    obtain ⟨hYplane, hYsub, hmY⟩ := hY
    exact eq_of_isStarPlane (X := X) (Y := Y) hP hT c hdeg hreg hXplane hYplane
      ⟨hxX, hYsub (mem_starLine_left hx)⟩
      ⟨hyX, hYsub (mem_starLine_right hy0)⟩ ⟨hmX, hmY⟩ hnc |>.symm

private theorem exists_mem_hypLine_of_mem_ptPerp_of_adj (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ)
    {u M : V} (hu : c u = 0) (hsub : ℓ ⊆ ptPerp Γ c {u}) (hM : c M = 1)
    (huM : Γ.Adj M u) : ∃ w ∈ ℓ, Γ.Adj M w := by
  classical
  obtain ⟨x, y, hx, hdist, hℓeq⟩ := hℓ
  rw [hℓeq] at hsub ⊢
  have hcardS : (starLine Γ c x y).ncard = t + 1 :=
    ncard_starLine_of_dist_four hP hT c hdeg hreg hx hdist
  have hS : starLine Γ c x y = spanSet Γ x y :=
    starLine_eq_spanSet hP hT c hx hdist
  have hu_notS : u ∉ starLine Γ c x y := by
    intro huS
    have hlt : 1 < (starLine Γ c x y).ncard := by
      rw [hcardS]
      have ht := two_le_t hP hT c hdeg
      omega
    obtain ⟨w', hw'S, hw'u⟩ := Set.exists_ne_of_one_lt_ncard hlt u
    have h4 : Γ.dist w' u = 4 := by
      rw [hS] at huS hw'S
      exact dist_eq_four_of_mem_span hP hT hdist hw'S huS hw'u
    have hle : Γ.dist w' u ≤ 2 := by
      have h := (mem_ptPerp.mp (hsub hw'S)).2 u (Set.mem_singleton u)
      simpa [SimpleGraph.dist_comm] using h
    omega
  have hw_dist : ∀ w ∈ starLine Γ c x y, Γ.dist w u = 2 := by
    intro w hw
    have hw_sub := hsub hw
    have hw0 : c w = 0 := (mem_ptPerp.mp hw_sub).1
    have hle : Γ.dist w u ≤ 2 := by
      have h := (mem_ptPerp.mp hw_sub).2 u (Set.mem_singleton u)
      simpa [SimpleGraph.dist_comm] using h
    have hwu : w ≠ u := fun h => hu_notS (h ▸ hw)
    exact dist_eq_two_of_le_two_of_ne hP hw0 hu hwu hle
  let f : ↥(starLine Γ c x y) → V := fun w => commonNeighbor hP (hw_dist w.1 w.2)
  have hfmem : ∀ w : ↥(starLine Γ c x y), f w ∈ Γ.neighborSet u := fun w =>
    commonNeighbor_adj_right hP (hw_dist w.1 w.2)
  have hfinj : Function.Injective f := by
    intro w w' hww'
    apply Subtype.ext
    by_contra hne
    have h4 : Γ.dist w.1 w'.1 = 4 := by
      have hw : w.1 ∈ spanSet Γ x y := by rw [← hS]; exact w.2
      have hw' : w'.1 ∈ spanSet Γ x y := by rw [← hS]; exact w'.2
      exact dist_eq_four_of_mem_span hP hT hdist hw hw' hne
    have hwL : Γ.Adj w.1 (f w) :=
      commonNeighbor_adj_left hP (hw_dist w.1 w.2)
    have hw'L : Γ.Adj (f w) w'.1 := by
      have h : Γ.Adj w'.1 (f w') :=
        commonNeighbor_adj_left hP (hw_dist w'.1 w'.2)
      rw [← hww'] at h
      exact h.symm
    have h2 : Γ.dist w.1 w'.1 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hwL hw'L hne
    omega
  have himg : (Set.range f).ncard = (starLine Γ c x y).ncard := by
    rw [Set.ncard_range_of_injective hfinj, Nat.card_coe_set_eq]
  have hsubN : Set.range f ⊆ Γ.neighborSet u := by
    rintro z ⟨w, rfl⟩
    exact hfmem w
  have hNcard : (Γ.neighborSet u).ncard = t + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg u, if_pos hu]
  have hrange : Set.range f = Γ.neighborSet u := by
    refine Set.eq_of_subset_of_ncard_le hsubN ?_
    rw [hNcard, himg, hcardS]
  have hMmem : M ∈ Γ.neighborSet u := huM.symm
  obtain ⟨w, hwM⟩ := hrange ▸ hMmem
  refine ⟨w.1, w.2, ?_⟩
  rw [← hwM]
  exact (commonNeighbor_adj_left hP (hw_dist w.1 w.2)).symm

private theorem not_exists_starPlane_superset_disjoint_line (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ)
    {M : V} (hM : c M = 1) (hmiss : ∀ w ∈ ℓ, ¬ Γ.Adj M w) {X : Set V}
    (hX : IsStarPlane Γ c X) (hMX : Γ.neighborSet M ⊆ X) (hℓX : ℓ ⊆ X) : False := by
  classical
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have hMcard : (Γ.neighborSet M).ncard = s + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg M, if_neg (by rw [hM]; decide)]
  rcases isStarPlane_cases hP hT c hdeg hreg hX with hXabs | hXnon
  · obtain ⟨u, hu, rfl⟩ := hXabs
    have huM : u ∈ Γ.neighborSet M := by
      by_contra huM
      have hdist : ∀ x ∈ Γ.neighborSet M, Γ.dist u x = 2 := by
        intro x hx
        have hxX : x ∈ ptPerp Γ c {u} := hMX hx
        have hx0 : c x = 0 := hxX.1
        have hle : Γ.dist x u ≤ 2 := hxX.2 u (Set.mem_singleton u)
        have hne : x ≠ u := fun h => huM (h ▸ hx)
        have h : Γ.dist x u = 2 := dist_eq_two_of_le_two_of_ne hP hx0 hu hne hle
        rwa [SimpleGraph.dist_comm]
      have h2 : 1 < (Γ.neighborSet M).ncard := by
        rw [hMcard]
        omega
      obtain ⟨x, hx, x', hx', hxx'⟩ := (Set.one_lt_ncard).mp h2
      have hnot : ¬ Γ.Adj u M := fun h => huM (h.symm)
      have hxM : Γ.Adj M x := hx
      have hx'M : Γ.Adj M x' := hx'
      exact hxx' (eq_of_adj_of_dist_two_of_not_adj (hP := hP) (c := c) hnot hxM hx'M
        (hdist x hx) (hdist x' hx'))
    have hsub : ℓ ⊆ ptPerp Γ c {u} := by
      intro w hw
      rw [mem_ptPerp]
      have hwu : w ∈ ptPerp Γ c {u} := hℓX hw
      exact hwu
    obtain ⟨w, hwℓ, hMw⟩ :=
      exists_mem_hypLine_of_mem_ptPerp_of_adj hP hT c hdeg hreg hℓ hu hsub hM huM
    exact hmiss w hwℓ hMw
  · have hov : IsOvoid Γ c X := hXnon.2
    have h1 := hov.2 M hM
    have hinter : Γ.neighborSet M ∩ X = Γ.neighborSet M := Set.inter_eq_left.mpr hMX
    rw [hinter, hMcard] at h1
    omega

private theorem ncard_starPlanes_superset_hypLine (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c)
    {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ) :
    {X | IsStarPlane Γ c X ∧ ℓ ⊆ X}.ncard = s + 1 := by
  classical
  let P : Set (Set V) := {X | IsStarPlane Γ c X ∧ ℓ ⊆ X}
  obtain ⟨M, hM, hmiss⟩ := exists_line_missing_hypLine hP hT c hdeg hreg hℓ
  have hMpoint : ∀ m : ↥(Γ.neighborSet M), c m.1 = 0 := fun m =>
    color_eq_zero_of_adj_of_color_eq_one hM m.2
  have hMnotℓ : ∀ m : ↥(Γ.neighborSet M), m.1 ∉ ℓ := fun m hm =>
    hmiss m.1 hm m.2
  let plane : ↥(Γ.neighborSet M) → Set V := fun m =>
    (existsUnique_starPlane_of_hypLine_and_point hP hT c hdeg hreg hii hℓ
      (hMpoint m) (hMnotℓ m)).choose
  have hplane : ∀ m : ↥(Γ.neighborSet M),
      IsStarPlane Γ c (plane m) ∧ ℓ ⊆ plane m ∧ m.1 ∈ plane m := fun m =>
    (existsUnique_starPlane_of_hypLine_and_point hP hT c hdeg hreg hii hℓ
      (hMpoint m) (hMnotℓ m)).choose_spec.1
  have hrange_sub : Set.range plane ⊆ P := by
    rintro X ⟨m, rfl⟩
    exact ⟨(hplane m).1, (hplane m).2.1⟩
  have hinj : Function.Injective plane := by
    intro m m' hmm'
    apply Subtype.ext
    by_contra hne
    have hmP : m.1 ∈ plane m := (hplane m).2.2
    have hm'P : m'.1 ∈ plane m := by
      rw [hmm']
      exact (hplane m').2.2
    have h2 : Γ.dist m.1 m'.1 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP m.2.symm m'.2 hne
    have hc : M = commonNeighbor hP h2 :=
      eq_commonNeighbor hP h2 m.2.symm m'.2.symm
    have hMsub : Γ.neighborSet M ⊆ plane m := by
      intro x hx
      have hxstar : x ∈ starLine Γ c m.1 m'.1 := by
        rw [starLine_eq_neighborSet hP hT c (hMpoint m) h2]
        rw [← hc]
        exact hx
      exact (hplane m).1.1.1.2 m.1 hmP m'.1 hm'P hne hxstar
    exact (not_exists_starPlane_superset_disjoint_line hP hT c hdeg hreg hℓ hM hmiss
      (hplane m).1 hMsub (hplane m).2.1).elim
  have hsurj : P ⊆ Set.range plane := by
    intro X hX
    obtain ⟨hXplane, hℓX⟩ := hX
    rcases isStarPlane_cases hP hT c hdeg hreg hXplane with hXabs | hXnon
    · obtain ⟨u, hu, rfl⟩ := hXabs
      have huNotM : u ∉ Γ.neighborSet M := by
        intro huM
        have hsub : ℓ ⊆ ptPerp Γ c {u} := hℓX
        obtain ⟨w, hwℓ, hMw⟩ :=
          exists_mem_hypLine_of_mem_ptPerp_of_adj hP hT c hdeg hreg hℓ hu hsub hM huM
        exact hmiss w hwℓ hMw
      have hdist3 : Γ.dist u M = 3 :=
        dist_eq_three_of_not_adj_of_color_ne hP c (fun h => huNotM h.symm)
          (by rw [hu, hM]; norm_num)
      let m : V := proj hP hdist3
      have hmM : Γ.Adj M m := proj_adj hP hdist3
      have hum : Γ.dist u m = 2 := proj_dist hP hdist3
      have hmX : m ∈ ptPerp Γ c {u} := by
        rw [mem_ptPerp]
        refine ⟨color_eq_zero_of_adj_of_color_eq_one hM hmM, ?_⟩
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        simpa [SimpleGraph.dist_comm] using le_of_eq hum
      let mN : ↥(Γ.neighborSet M) := ⟨m, hmM⟩
      have huniq :=
        (existsUnique_starPlane_of_hypLine_and_point hP hT c hdeg hreg hii hℓ
          (hMpoint mN) (hMnotℓ mN)).unique (hplane mN) ⟨hXplane, hℓX, hmX⟩
      exact ⟨mN, huniq⟩
    · have hov : IsOvoid Γ c X := hXnon.2
      have h1 : (Γ.neighborSet M ∩ X).ncard = 1 := hov.2 M hM
      have hpos : 0 < (Γ.neighborSet M ∩ X).ncard := by rw [h1]; omega
      obtain ⟨m, hmM, hmX⟩ :=
        (Set.ncard_pos (s := Γ.neighborSet M ∩ X)).mp hpos
      let mN : ↥(Γ.neighborSet M) := ⟨m, hmM⟩
      have huniq :=
        (existsUnique_starPlane_of_hypLine_and_point hP hT c hdeg hreg hii hℓ
          (hMpoint mN) (hMnotℓ mN)).unique (hplane mN) ⟨hXplane, hℓX, hmX⟩
      exact ⟨mN, huniq⟩
  have hrange : Set.range plane = P := Set.Subset.antisymm hrange_sub hsurj
  have hMcard : (Γ.neighborSet M).ncard = s + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg M, if_neg (by rw [hM]; decide)]
  calc
    P.ncard = (Set.range plane).ncard := by rw [hrange]
    _ = (Γ.neighborSet M).ncard := by
      rw [Set.ncard_range_of_injective hinj, Nat.card_coe_set_eq]
    _ = s + 1 := hMcard

theorem ptPerp_starLine_eq_traceSet (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {x y : V} (hx : c x = 0) (hxy : Γ.dist x y = 4) :
    ptPerp Γ c (starLine Γ c x y) = traceSet Γ x y := by
  classical
  have hy0 : c y = 0 := by
    have h : c x = c y :=
      (hP.eq_iff_even_dist c x y).2 (by rw [hxy]; exact ⟨2, by norm_num⟩)
    rw [← h]
    exact hx
  ext u
  constructor
  · intro hu
    rw [mem_ptPerp] at hu
    have hux_le : Γ.dist u x ≤ 2 := hu.2 x (mem_starLine_left hx)
    have huy_le : Γ.dist u y ≤ 2 := hu.2 y (mem_starLine_right hy0)
    have hu0 : c u = 0 := hu.1
    have hux_ne : u ≠ x := by
      intro h
      rw [h] at huy_le
      omega
    have huy_ne : u ≠ y := by
      intro h
      rw [h, SimpleGraph.dist_comm] at hux_le
      omega
    have hux2 : Γ.dist u x = 2 :=
      dist_eq_two_of_le_two_of_ne hP hu0 hx hux_ne (by simpa [SimpleGraph.dist_comm] using hux_le)
    have huy2 : Γ.dist u y = 2 :=
      dist_eq_two_of_le_two_of_ne hP hu0 hy0 huy_ne (by simpa [SimpleGraph.dist_comm] using huy_le)
    exact ⟨by rw [SimpleGraph.dist_comm]; exact hux2,
      by rw [SimpleGraph.dist_comm]; exact huy2⟩
  · intro hu
    rw [mem_ptPerp]
    refine ⟨color_eq_zero_of_dist_eq_two hP hx hu.1, ?_⟩
    intro w hw
    have hw' : w ∈ spanSet Γ x y := by
      rw [← starLine_eq_spanSet hP hT c hx hxy]
      exact hw
    have h : Γ.dist w u = 2 :=
      dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hw' hu
    simpa [SimpleGraph.dist_comm] using le_of_eq h

private theorem ncard_absPlanes_superset_hypLine (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ) :
    {X | IsAbsPlane Γ c X ∧ ℓ ⊆ X}.ncard = t + 1 := by
  classical
  obtain ⟨x, y, hx, hdist, hℓeq⟩ := hℓ
  rw [hℓeq]
  have htrace : ptPerp Γ c (starLine Γ c x y) = traceSet Γ x y :=
    ptPerp_starLine_eq_traceSet hP hT c hx hdist
  let A : Set (Set V) := {X | IsAbsPlane Γ c X ∧ starLine Γ c x y ⊆ X}
  let g : ↥(ptPerp Γ c (starLine Γ c x y)) → Set V := fun u =>
    ptPerp Γ c {u.1}
  have hg : ∀ u : ↥(ptPerp Γ c (starLine Γ c x y)),
      IsAbsPlane Γ c (g u) ∧ starLine Γ c x y ⊆ g u := by
    intro u
    refine ⟨⟨u.1, u.2.1, rfl⟩, ?_⟩
    intro w hw
    rw [mem_ptPerp]
    refine ⟨color_eq_zero_of_mem_starLine hw, ?_⟩
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact by
      have h := u.2.2 w hw
      simpa [SimpleGraph.dist_comm] using h
  have hginj : Function.Injective g := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    have hu_trace : u.1 ∈ traceSet Γ x y := by
      rw [← htrace]
      exact u.2
    have hv_trace : v.1 ∈ traceSet Γ x y := by
      rw [← htrace]
      exact v.2
    have h4 : Γ.dist u.1 v.1 = 4 :=
      dist_eq_four_of_mem_trace hP hdist hu_trace hv_trace hne
    have huv' : ptPerp Γ c {u.1} = ptPerp Γ c {v.1} := huv
    have hv_perp : v.1 ∈ ptPerp Γ c {u.1} := by
      rw [huv']
      rw [mem_ptPerp]
      exact ⟨v.2.1, by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        simp⟩
    have h2 : Γ.dist u.1 v.1 ≤ 2 := by
      have h := (mem_ptPerp.mp hv_perp).2 u.1 (Set.mem_singleton u.1)
      simpa [SimpleGraph.dist_comm] using h
    omega
  have hrange_sub : Set.range g ⊆ A := by
    rintro X ⟨u, rfl⟩
    exact hg u
  have hsurj : A ⊆ Set.range g := by
    rintro X ⟨hXabs, hℓX⟩
    obtain ⟨u, hu, rfl⟩ := hXabs
    have hu_trace : u ∈ ptPerp Γ c (starLine Γ c x y) := by
      rw [mem_ptPerp]
      refine ⟨hu, ?_⟩
      intro w hw
      have hwu : w ∈ ptPerp Γ c {u} := hℓX hw
      have h := (mem_ptPerp.mp hwu).2 u (Set.mem_singleton u)
      simpa [SimpleGraph.dist_comm] using h
    exact ⟨⟨u, hu_trace⟩, rfl⟩
  have hrange : Set.range g = A := Set.Subset.antisymm hrange_sub hsurj
  have hcard : (ptPerp Γ c (starLine Γ c x y)).ncard = t + 1 := by
    rw [htrace]
    have hy0 : c y = 0 := by
      have h : c x = c y :=
        (hP.eq_iff_even_dist c x y).2 (by rw [hdist]; exact ⟨2, by norm_num⟩)
      rw [← h]
      exact hx
    rw [ncard_trace hP hdist, hdeg x, if_pos hx]
  calc
    A.ncard = (Set.range g).ncard := by rw [hrange]
    _ = (ptPerp Γ c (starLine Γ c x y)).ncard := by
      rw [Set.ncard_range_of_injective hginj, Nat.card_coe_set_eq]
    _ = t + 1 := hcard

theorem ncard_planes_superset_hypLine (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c) {ℓ : Set V}
    (hℓ : IsHypLine Γ c ℓ) :
    {X | IsStarPlane Γ c X ∧ ℓ ⊆ X}.ncard = s + 1 ∧
      {X | IsAbsPlane Γ c X ∧ ℓ ⊆ X}.ncard = t + 1 ∧
      {X | IsNonabsPlane Γ c X ∧ ℓ ⊆ X}.ncard = s - t := by
  classical
  let P : Set (Set V) := {X | IsStarPlane Γ c X ∧ ℓ ⊆ X}
  let A : Set (Set V) := {X | IsAbsPlane Γ c X ∧ ℓ ⊆ X}
  let N : Set (Set V) := {X | IsNonabsPlane Γ c X ∧ ℓ ⊆ X}
  have hPUN : P = A ∪ N := by
    ext X
    constructor
    · rintro ⟨hXplane, hℓX⟩
      rcases isStarPlane_cases hP hT c hdeg hreg hXplane with hXabs | hXnon
      · exact Or.inl ⟨hXabs, hℓX⟩
      · exact Or.inr ⟨hXnon, hℓX⟩
    · rintro (⟨hXabs, hℓX⟩ | ⟨hXnon, hℓX⟩)
      · obtain ⟨u, hu, rfl⟩ := hXabs
        exact ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hu, hℓX⟩
      · exact ⟨hXnon.1, hℓX⟩
  have hdisj : Disjoint A N := by
    rw [Set.disjoint_left]
    intro X hXA hXN
    have h1 : X.ncard = s * t + s + 1 := ncard_of_isAbsPlane hP hT c hdeg hXA.1
    have h2 : X.ncard = s * t + 1 := ncard_of_isNonabsPlane hP hT c hdeg hXN.1
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    omega
  have hPcard : P.ncard = s + 1 :=
    ncard_starPlanes_superset_hypLine hP hT c hdeg hreg hii hℓ
  have hAcard : A.ncard = t + 1 :=
    ncard_absPlanes_superset_hypLine hP hT c hdeg hreg hℓ
  have hsum : P.ncard = A.ncard + N.ncard := by
    rw [hPUN]
    exact Set.ncard_union_eq hdisj
  have hNcard : N.ncard = s - t := by
    omega
  exact ⟨hPcard, hAcard, hNcard⟩

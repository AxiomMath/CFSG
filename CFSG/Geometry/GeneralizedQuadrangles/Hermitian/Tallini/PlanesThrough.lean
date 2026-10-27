module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Varieties2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section StarLineAPI

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem color_eq_of_dist_four (hP : IsGeneralizedPolygon Γ 4) {c : Γ.Coloring (Fin 2)}
    {x y : V} (hxy : Γ.dist x y = 4) : c x = c y :=
  (hP.eq_iff_even_dist c x y).2 (by rw [hxy]; exact ⟨2, by norm_num⟩)

theorem IsHypLine.isStarLine (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ) : IsStarLine Γ c ℓ := by
  obtain ⟨x, y, hx, h4, rfl⟩ := hℓ
  refine ⟨x, y, hx, ?_, ?_, rfl⟩
  · rw [← color_eq_of_dist_four hP h4]
    exact hx
  · intro hxy
    rw [hxy] at h4
    simp at h4

theorem IsHypLine.ncard (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ) :
    ℓ.ncard = t + 1 := by
  obtain ⟨x, y, hx, h4, rfl⟩ := hℓ
  exact ncard_starLine_of_dist_four hP hT c hdeg hreg hx h4

theorem IsHypLine.color (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ) {z : V} (hz : z ∈ ℓ) :
    c z = 0 := by
  obtain ⟨x, y, hx, h4, rfl⟩ := hℓ
  exact color_eq_zero_of_mem_starLine hz

theorem IsHypLine.dist_eq_four (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ) {z z' : V}
    (hz : z ∈ ℓ) (hz' : z' ∈ ℓ) (hne : z ≠ z') : Γ.dist z z' = 4 := by
  obtain ⟨x, y, hx, h4, rfl⟩ := hℓ
  have hspan : starLine Γ c x y = spanSet Γ x y := starLine_eq_spanSet hP hT c hx h4
  rw [hspan] at hz hz'
  exact dist_eq_four_of_mem_span hP hT h4 hz hz' hne

theorem exists_starLine_eq_of_mem_of_isHypLine (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {c : Γ.Coloring (Fin 2)} {ℓ : Set V} (hℓ : IsHypLine Γ c ℓ)
    {x : V} (hxℓ : x ∈ ℓ) (hx : c x = 0) :
    ∃ y, Γ.dist x y = 4 ∧ ℓ = starLine Γ c x y := by
  obtain ⟨a, b, ha, h4, rfl⟩ := hℓ
  have hspan : starLine Γ c a b = spanSet Γ a b := starLine_eq_spanSet hP hT c ha h4
  have hxspan : x ∈ spanSet Γ a b := by
    rw [← hspan]
    exact hxℓ
  by_cases hxa : x = a
  · subst hxa
    exact ⟨b, h4, rfl⟩
  · have hbspan : b ∈ spanSet Γ a b := right_mem_spanSet h4
    by_cases hxb : x = b
    · rw [hxb]
      exact ⟨a, by rw [SimpleGraph.dist_comm]; exact h4, starLine_comm a b⟩
    · obtain ⟨hdist, hspan_eq, -⟩ :=
        span_eq_of_mem hP hT h4 hxspan hbspan hxb
      refine ⟨b, hdist, ?_⟩
      rw [hspan, starLine_eq_spanSet hP hT c hx hdist]
      exact hspan_eq.symm

end StarLineAPI

section HypLinesThrough

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ncard_hypLines_through (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {x : V} (hx : c x = 0) :
    {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ}.ncard = s ^ 2 := by
  classical
  have ht : 0 < t := by
    have := two_le_t hP hT c hdeg
    omega
  let Opp : Finset V := Finset.univ.filter fun y => Γ.dist x y = 4
  let L : Finset (Set V) := Finset.univ.filter fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ
  have hOpp : Opp.card = s ^ 2 * t := by
    simpa [Opp] using card_opposite hP hT c hdeg hx
  have hmap : ∀ y ∈ Opp, starLine Γ c x y ∈ L := by
    intro y hy
    rw [Finset.mem_filter] at hy
    have hy4 : Γ.dist x y = 4 := by simpa [Opp] using hy.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact ⟨x, y, hx, hy4, rfl⟩
    · exact mem_starLine_left hx
  have hfiber : ∀ ℓ ∈ L, (Opp.filter fun y => starLine Γ c x y = ℓ).card = t := by
    intro ℓ hℓ
    rw [Finset.mem_filter] at hℓ
    obtain ⟨-, hℓhyp, hxℓ⟩ := hℓ
    have hline : (Finset.univ.filter fun z : V => z ∈ ℓ).card = t + 1 := by
      have hcoe : ((Finset.univ.filter fun z : V => z ∈ ℓ : Finset V) : Set V) = ℓ := by
        ext z
        simp
      rw [← Set.ncard_coe_finset, hcoe, IsHypLine.ncard hP hT c hdeg hreg hℓhyp]
    have hset : (Opp.filter fun y => starLine Γ c x y = ℓ) =
        (Finset.univ.filter fun z : V => z ∈ ℓ).erase x := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Opp]
      constructor
      · rintro ⟨hz4, hzℓ⟩
        refine ⟨?_, ?_⟩
        · rintro rfl
          simp at hz4
        · have hz0 : c z = 0 := by
            rw [← color_eq_of_dist_four hP hz4]
            exact hx
          rw [← hzℓ, starLine_comm]
          exact mem_starLine_left hz0
      · rintro ⟨hxz, hzℓ⟩
        have hzx : x ≠ z := fun h => hxz h.symm
        refine ⟨IsHypLine.dist_eq_four hP hT hℓhyp hxℓ hzℓ hzx, ?_⟩
        exact (starLine_eq_of_isStarLine_of_mem hP hT (IsHypLine.isStarLine hP hℓhyp)
          hxℓ hzℓ hzx).symm
    rw [hset, Finset.card_erase_of_mem (by simp [hxℓ]), hline]
    omega
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun y => starLine Γ c x y)
    (s := Opp) (t := L) hmap
  rw [hsum, Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul] at hOpp
  have hLcard : L.card = s ^ 2 := Nat.eq_of_mul_eq_mul_right ht hOpp
  have hcoe : ((L : Set (Set V))) = {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ} := by
    ext ℓ
    simp [L]
  rw [← hcoe, Set.ncard_coe_finset, hLcard]

end HypLinesThrough


section PlaneLemmas

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem isLinearVariety_inter {c : Γ.Coloring (Fin 2)} {X Y : Set V}
    (hX : IsLinearVariety Γ c X) (hY : IsLinearVariety Γ c Y) :
    IsLinearVariety Γ c (X ∩ Y) := by
  refine ⟨fun z hz => hX.1 z hz.1, fun a ha b hb hab z hz => ⟨?_, ?_⟩⟩
  · exact hX.2 a ha.1 b hb.1 hab hz
  · exact hY.2 a ha.2 b hb.2 hab hz

theorem not_isStarCollinear_of_not_mem_starLine (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {c : Γ.Coloring (Fin 2)} {a b z : V} (hab : a ≠ b)
    (hz : z ∉ starLine Γ c a b) : ¬ IsStarCollinear Γ c a b z := by
  rintro ⟨Z, hZ, haz, hbz, hzz⟩
  have hZeq : starLine Γ c a b = Z :=
    (starLine_eq_of_isStarLine_of_mem hP hT hZ haz hbz hab).symm
  exact hz (by rw [hZeq]; exact hzz)

theorem dist_eq_four_of_mem_of_isOvoid (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {X : Set V} (hO : IsOvoid Γ c X) {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) : Γ.dist x y = 4 := by
  classical
  have hx0 : c x = 0 := hO.1 x hx
  have hy0 : c y = 0 := hO.1 y hy
  have heven : Even (Γ.dist x y) := (hP.eq_iff_even_dist c x y).1 (hx0.trans hy0.symm)
  have hle : Γ.dist x y ≤ 4 := hP.dist_le (by norm_num) x y
  have hne0 : Γ.dist x y ≠ 0 := fun h => hxy ((hP.connected.dist_eq_zero_iff).mp h)
  by_contra h4
  have h2 : Γ.dist x y = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  let L := commonNeighbor hP h2
  have hxL : Γ.Adj x L := commonNeighbor_adj_left hP h2
  have hyL : Γ.Adj y L := commonNeighbor_adj_right hP h2
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hx0 hxL
  have hcont : 1 < (Γ.neighborSet L ∩ X).ncard := by
    rw [Set.one_lt_ncard]
    exact ⟨x, ⟨hxL.symm, hx⟩, y, ⟨hyL.symm, hy⟩, hxy⟩
  have hone : (Γ.neighborSet L ∩ X).ncard = 1 := hO.2 L hL1
  omega

theorem ne_ptPerp_of_isNonabsPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {X : Set V}
    (hX : IsNonabsPlane Γ c X) {x : V} (hxX : x ∈ X) : X ≠ ptPerp Γ c {x} := by
  intro heq
  have hx0 : c x = 0 := (hX.1.1.1.1) x hxX
  have h1 : X.ncard = s * t + 1 := ncard_of_isOvoid hP hT c hdeg hX.2
  have h2 : (ptPerp Γ c {x}).ncard = s * t + s + 1 :=
    ncard_ptPerp_singleton hP hT c hdeg hx0
  rw [heq, h2] at h1
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  omega

theorem neighborSet_subset_ptPerp (hP : IsGeneralizedPolygon Γ 4) {c : Γ.Coloring (Fin 2)}
    {u L : V} (hL1 : c L = 1) (huL : Γ.Adj u L) :
    Γ.neighborSet L ⊆ ptPerp Γ c {u} := by
  intro z hz
  rw [mem_ptPerp]
  refine ⟨color_eq_zero_of_adj_of_color_eq_one hL1 hz, ?_⟩
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  rw [hv]
  by_cases hzu : z = u
  · rw [hzu]
    simp
  · have h2 : Γ.dist z u = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hz.symm huL.symm hzu
    omega

theorem ncard_opposite_mem_ptPerp (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {u x : V}
    (hu : c u = 0) (hxX : x ∈ ptPerp Γ c {u}) (hux : u ≠ x) :
    {y | y ∈ ptPerp Γ c {u} ∧ Γ.dist x y = 4}.ncard = s * t := by
  classical
  have hx0 : c x = 0 := (mem_ptPerp.1 hxX).1
  have hxu_le : Γ.dist x u ≤ 2 := (mem_ptPerp.1 hxX).2 u (by simp)
  have hux2 : Γ.dist u x = 2 := by
    have heven : Even (Γ.dist u x) := (hP.eq_iff_even_dist c u x).1 (hu.trans hx0.symm)
    have hle : Γ.dist u x ≤ 2 := by rw [SimpleGraph.dist_comm]; exact hxu_le
    have hne0 : Γ.dist u x ≠ 0 := fun h => hux ((hP.connected.dist_eq_zero_iff).mp h)
    obtain ⟨k, hk⟩ := heven
    omega
  let L := commonNeighbor hP hux2
  have hLu : Γ.Adj u L := commonNeighbor_adj_left hP hux2
  have hLx : Γ.Adj x L := commonNeighbor_adj_right hP hux2
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hu hLu
  have hLdeg : (Γ.neighborSet L).ncard = s + 1 := by
    rw [ncard_neighborSet, hdeg, if_neg (by rw [hL1]; decide)]
  have hsub : Γ.neighborSet L ⊆ ptPerp Γ c {u} := neighborSet_subset_ptPerp hP hL1 hLu
  have hYset : {y | y ∈ ptPerp Γ c {u} ∧ Γ.dist x y = 4} =
      ptPerp Γ c {u} \ Γ.neighborSet L := by
    ext y
    constructor
    · rintro ⟨hyX, hy4⟩
      refine ⟨hyX, ?_⟩
      intro hyL
      have hxy : x ≠ y := by
        rintro rfl
        simp at hy4
      have h2 : Γ.dist x y = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hLx hyL hxy
      omega
    · rintro ⟨hyX, hyL⟩
      refine ⟨hyX, ?_⟩
      have hy0 : c y = 0 := (mem_ptPerp.1 hyX).1
      have hyu_le : Γ.dist y u ≤ 2 := (mem_ptPerp.1 hyX).2 u (by simp)
      have huy : u ≠ y := by
        intro h
        exact hyL (h ▸ hLu).symm
      have huy2 : Γ.dist u y = 2 := by
        have heven : Even (Γ.dist u y) := (hP.eq_iff_even_dist c u y).1 (hu.trans hy0.symm)
        have hle : Γ.dist u y ≤ 2 := by rw [SimpleGraph.dist_comm]; exact hyu_le
        have hne0 : Γ.dist u y ≠ 0 := fun h => huy ((hP.connected.dist_eq_zero_iff).mp h)
        obtain ⟨k, hk⟩ := heven
        omega
      have hxy : x ≠ y := by
        intro h
        exact hyL (h ▸ hLx.symm)
      have hxy2 : Γ.dist x y ≠ 2 := by
        intro h2
        obtain ⟨w, hw, -⟩ := existsUnique_commonNeighbor_of_pairwise_dist_two hP h2
          (by rw [SimpleGraph.dist_comm]; exact hux2)
          (by rw [SimpleGraph.dist_comm]; exact huy2)
        have hwL : w = L :=
          (existsUnique_commonNeighbor hP hux2).unique ⟨hw.2.2, hw.1⟩ ⟨hLu, hLx⟩
        have hyL' : Γ.Adj y L := by
          have h := hw.2.1
          rw [hwL] at h
          exact h
        exact hyL hyL'.symm
      have heven : Even (Γ.dist x y) := (hP.eq_iff_even_dist c x y).1 (hx0.trans hy0.symm)
      have hle4 : Γ.dist x y ≤ 4 := hP.dist_le (by norm_num) x y
      have hne0 : Γ.dist x y ≠ 0 := fun h => hxy ((hP.connected.dist_eq_zero_iff).mp h)
      obtain ⟨k, hk⟩ := heven
      have hk2 : k ≤ 2 := by omega
      interval_cases k <;> omega
  rw [hYset, Set.ncard_sdiff (s := Γ.neighborSet L) (t := ptPerp Γ c {u}) hsub,
    ncard_ptPerp_singleton hP hT c hdeg hu, hLdeg]
  omega

theorem ncard_opposite_mem_of_isStarPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsStarPlane Γ c X)
    {x : V} (hxX : x ∈ X) (hXx : X ≠ ptPerp Γ c {x}) :
    {y | y ∈ X ∧ Γ.dist x y = 4}.ncard = s * t := by
  classical
  rcases isStarPlane_cases hP hT c hdeg hreg hX with habs | hnon
  · obtain ⟨u, hu, rfl⟩ := habs
    have hux : u ≠ x := by
      intro h
      rw [h] at hXx
      exact hXx rfl
    exact ncard_opposite_mem_ptPerp hP hT c hdeg hu hxX hux
  · have hO : IsOvoid Γ c X := hnon.2
    have hYeq : {y | y ∈ X ∧ Γ.dist x y = 4} = X \ {x} := by
      ext y
      constructor
      · rintro ⟨hyX, hy4⟩
        exact ⟨hyX, by rintro rfl; simp at hy4⟩
      · rintro ⟨hyX, hyx⟩
        exact ⟨hyX, dist_eq_four_of_mem_of_isOvoid hP hT hO hxX hyX
          (fun h => hyx h.symm)⟩
    rw [hYeq, Set.ncard_sdiff (s := {x}) (t := X) (by simpa using hxX),
      ncard_of_isOvoid hP hT c hdeg hO]
    simp

end PlaneLemmas


section HypLinesInPlane

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ncard_hypLines_through_subset (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsStarPlane Γ c X)
    {x : V} (hxX : x ∈ X) (hXx : X ≠ ptPerp Γ c {x}) :
    {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ X}.ncard = s := by
  classical
  have hx0 : c x = 0 := hX.1.1.1 x hxX
  have ht : 0 < t := by
    have := two_le_t hP hT c hdeg
    omega
  let Y : Finset V := Finset.univ.filter fun y => y ∈ X ∧ Γ.dist x y = 4
  let L : Finset (Set V) := Finset.univ.filter fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ X
  have hYcard : Y.card = s * t := by
    rw [← Set.ncard_coe_finset]
    have hYcoe : ((Y : Set V)) = {y | y ∈ X ∧ Γ.dist x y = 4} := by
      ext y
      simp [Y]
    rw [hYcoe]
    exact ncard_opposite_mem_of_isStarPlane hP hT c hdeg hreg hX hxX hXx
  have hmap : ∀ y ∈ Y, starLine Γ c x y ∈ L := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨-, hyX, hy4⟩ := hy
    have hxy : x ≠ y := by
      rintro rfl
      simp at hy4
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · exact ⟨x, y, hx0, hy4, rfl⟩
    · exact mem_starLine_left hx0
    · exact hX.1.1.2 x hxX y hyX hxy
  have hfiber : ∀ ℓ ∈ L, (Y.filter fun y => starLine Γ c x y = ℓ).card = t := by
    intro ℓ hℓ
    rw [Finset.mem_filter] at hℓ
    obtain ⟨-, hℓhyp, hxℓ, hℓX⟩ := hℓ
    have hline : (Finset.univ.filter fun z : V => z ∈ ℓ).card = t + 1 := by
      have hcoe : ((Finset.univ.filter fun z : V => z ∈ ℓ : Finset V) : Set V) = ℓ := by
        ext z
        simp
      rw [← Set.ncard_coe_finset, hcoe, IsHypLine.ncard hP hT c hdeg hreg hℓhyp]
    have hset : (Y.filter fun y => starLine Γ c x y = ℓ) =
        (Finset.univ.filter fun z : V => z ∈ ℓ).erase x := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Y]
      constructor
      · rintro ⟨⟨hzX, hz4⟩, hzℓ⟩
        refine ⟨?_, ?_⟩
        · rintro rfl
          simp at hz4
        · have hz0 : c z = 0 := by
            rw [← color_eq_of_dist_four hP hz4]
            exact hx0
          rw [← hzℓ, starLine_comm]
          exact mem_starLine_left hz0
      · rintro ⟨hxz, hzℓ⟩
        have hzx : x ≠ z := fun h => hxz h.symm
        refine ⟨⟨hℓX hzℓ, IsHypLine.dist_eq_four hP hT hℓhyp hxℓ hzℓ hzx⟩, ?_⟩
        exact (starLine_eq_of_isStarLine_of_mem hP hT (IsHypLine.isStarLine hP hℓhyp)
          hxℓ hzℓ hzx).symm
    rw [hset, Finset.card_erase_of_mem (by simp [hxℓ]), hline]
    omega
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun y => starLine Γ c x y)
    (s := Y) (t := L) hmap
  rw [hsum, Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul] at hYcard
  have hLcard : L.card = s := Nat.eq_of_mul_eq_mul_right ht hYcard
  have hcoe : ((L : Set (Set V))) = {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ X} := by
    ext ℓ
    simp [L]
  rw [← hcoe, Set.ncard_coe_finset, hLcard]

end HypLinesInPlane

section NonabsPlanesThrough

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ncard_nonabsPlanes_through (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c) {x : V}
    (hx : c x = 0) : {X | IsNonabsPlane Γ c X ∧ x ∈ X}.ncard = s * (s - t) := by
  classical
  let L : Finset (Set V) := Finset.univ.filter fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ
  let M : Finset (Set V) := Finset.univ.filter fun X => IsNonabsPlane Γ c X ∧ x ∈ X
  have hLcard : L.card = s ^ 2 := by
    rw [← Set.ncard_coe_finset]
    have hcoe : ((L : Set (Set V))) = {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ} := by
      ext ℓ
      simp [L]
    rw [hcoe, ncard_hypLines_through hP hT c hdeg hreg hx]
  have hrow : ∀ ℓ ∈ L, (M.filter fun X => ℓ ⊆ X).card = s - t := by
    intro ℓ hℓ
    rw [Finset.mem_filter] at hℓ
    obtain ⟨-, hℓhyp, hxℓ⟩ := hℓ
    have hset : (M.filter fun X => ℓ ⊆ X) =
        Finset.univ.filter (fun X : Set V => IsNonabsPlane Γ c X ∧ ℓ ⊆ X) := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, M]
      constructor
      · rintro ⟨⟨hXnon, -⟩, hℓX⟩
        exact ⟨hXnon, hℓX⟩
      · rintro ⟨hXnon, hℓX⟩
        exact ⟨⟨hXnon, hℓX hxℓ⟩, hℓX⟩
    rw [hset, ← Set.ncard_coe_finset]
    have hcoe : ((Finset.univ.filter
        (fun X : Set V => IsNonabsPlane Γ c X ∧ ℓ ⊆ X) : Finset (Set V)) : Set (Set V)) =
        {X | IsNonabsPlane Γ c X ∧ ℓ ⊆ X} := by
      ext X
      simp
    rw [hcoe]
    exact (ncard_planes_superset_hypLine hP hT c hdeg hreg hii hℓhyp).2.2
  have hcol : ∀ X ∈ M, (L.filter fun ℓ => ℓ ⊆ X).card = s := by
    intro X hX
    rw [Finset.mem_filter] at hX
    obtain ⟨-, hXnon, hxX⟩ := hX
    have hset : (L.filter fun ℓ => ℓ ⊆ X) =
        Finset.univ.filter (fun ℓ : Set V => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ X) := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, L]
      constructor
      · rintro ⟨⟨hℓhyp, hxℓ⟩, hℓX⟩
        exact ⟨hℓhyp, hxℓ, hℓX⟩
      · rintro ⟨hℓhyp, hxℓ, hℓX⟩
        exact ⟨⟨hℓhyp, hxℓ⟩, hℓX⟩
    rw [hset, ← Set.ncard_coe_finset]
    have hcoe : ((Finset.univ.filter
        (fun ℓ : Set V => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ X) : Finset (Set V)) : Set (Set V)) =
        {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ X} := by
      ext ℓ
      simp
    rw [hcoe]
    exact ncard_hypLines_through_subset hP hT c hdeg hreg hXnon.1 hxX
      (ne_ptPerp_of_isNonabsPlane hP hT c hdeg hXnon hxX)
  have hswap : (∑ ℓ ∈ L, (M.filter fun X => ℓ ⊆ X).card)
      = ∑ X ∈ M, (L.filter fun ℓ => ℓ ⊆ X).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have h1 : (∑ ℓ ∈ L, (M.filter fun X => ℓ ⊆ X).card) = L.card * (s - t) := by
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, smul_eq_mul]
  have h2 : (∑ X ∈ M, (L.filter fun ℓ => ℓ ⊆ X).card) = M.card * s := by
    rw [Finset.sum_congr rfl hcol, Finset.sum_const, smul_eq_mul]
  have heq : L.card * (s - t) = M.card * s := by
    rw [← h1, hswap, h2]
  have hs : 0 < s := by
    have := two_le_s hP hT c hdeg
    omega
  have heq' : s ^ 2 * (s - t) = M.card * s := by
    rw [← hLcard]
    exact heq
  have hmul : (s * (s - t)) * s = M.card * s := by
    rw [mul_comm (s * (s - t)) s, ← heq']
    ring
  have hMcard : M.card = s * (s - t) := (Nat.eq_of_mul_eq_mul_right hs hmul).symm
  have hcoe : ((M : Set (Set V))) = {X | IsNonabsPlane Γ c X ∧ x ∈ X} := by
    ext X
    simp [M]
  rw [← hcoe, Set.ncard_coe_finset, hMcard]

end NonabsPlanesThrough


section InterCases

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem inter_cases (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X Y : Set V} (hX : IsStarPlane Γ c X)
    (hY : IsStarPlane Γ c Y) (hXY : X ≠ Y) :
    X ∩ Y = ∅ ∨ (∃ x, X ∩ Y = {x}) ∨ IsStarLine Γ c (X ∩ Y) := by
  classical
  have hlin : IsLinearVariety Γ c (X ∩ Y) := isLinearVariety_inter hX.1.1 hY.1.1
  by_cases h2 : ∃ a b, a ∈ X ∩ Y ∧ b ∈ X ∩ Y ∧ a ≠ b
  · obtain ⟨a, b, ha, hb, hab⟩ := h2
    right
    right
    refine ⟨a, b, hlin.1 a ha, hlin.1 b hb, hab, ?_⟩
    refine Set.Subset.antisymm ?_ (hlin.2 a ha b hb hab)
    intro z hz
    by_cases hza : z = a
    · rw [hza]
      exact mem_starLine_left (hlin.1 a ha)
    · by_contra hznot
      have hnc : ¬ IsStarCollinear Γ c a b z :=
        not_isStarCollinear_of_not_mem_starLine hP hT hab hznot
      exact hXY (eq_of_isStarPlane hP hT c hdeg hreg hX hY ha hb hz hnc)
  · by_cases hne : (X ∩ Y).Nonempty
    · right
      left
      obtain ⟨x, hx⟩ := hne
      refine ⟨x, ?_⟩
      ext z
      constructor
      · intro hz
        by_contra hzx
        exact h2 ⟨z, x, hz, hx, hzx⟩
      · intro hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hx
    · left
      exact Set.not_nonempty_iff_eq_empty.mp hne

end InterCases


end CFSG.Geometry.GeneralizedQuadrangles

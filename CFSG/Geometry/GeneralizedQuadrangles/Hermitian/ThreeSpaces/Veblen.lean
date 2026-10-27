module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.SubquadrangleTallini2
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Pasch2
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Traces

public section
namespace CFSG.Geometry.GeneralizedQuadrangles
open SimpleGraph CFSG.Geometry.GeneralizedPolygons
universe u
variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}
theorem isThreespace_of_mem_isThreeBundle {β : Set (Set V)}
    (hβ : IsThreeBundle Γ c q β) {E : Set V} (hE : E ∈ β) : IsThreespace Γ c q E := by
  rcases hβ with ⟨T, -, rfl⟩ | ⟨L, hL, rfl⟩
  · exact hE.1
  · obtain ⟨x, hxL, rfl⟩ := hE
    exact Or.inl ⟨x, color_eq_zero_of_adj_of_color_eq_one hL hxL, rfl⟩
private theorem mem_ptPerp_self {x : V} (hx : c x = 0) : x ∈ ptPerp Γ c {x} := by
  rw [mem_ptPerp]
  exact ⟨hx, fun a ha => by
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simp⟩
private theorem color_zero_of_dist_le_two (hΓ : IsThasQuadrangle Γ c q) {a b x : V}
    (ha : c a = 0) (hb : c b = 0) (hab : Γ.dist a b = 4) (hax : Γ.dist a x ≤ 2)
    (hbx : Γ.dist b x ≤ 2) : c x = 0 := by
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  by_contra hx0
  have hca : c a ≠ c x := by
    rw [ha]
    exact fun h => hx0 h.symm
  have hcb : c b ≠ c x := by
    rw [hb]
    exact fun h => hx0 h.symm
  have hodd1 : Odd (Γ.dist a x) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact hca ((hP.eq_iff_even_dist c a x).2 heven)
  have hodd2 : Odd (Γ.dist b x) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact hcb ((hP.eq_iff_even_dist c b x).2 heven)
  obtain ⟨k, hk⟩ := hodd1
  obtain ⟨l, hl⟩ := hodd2
  have ha1 : Γ.dist a x = 1 := by omega
  have hb1 : Γ.dist b x = 1 := by omega
  have hxb : Γ.dist x b = 1 := by rw [SimpleGraph.dist_comm]; exact hb1
  have htri := hP.connected.dist_triangle (u := a) (v := x) (w := b)
  rw [ha1, hxb] at htri
  omega
private theorem isStarPlane_subquadrangle_of_subset (hΓ : IsThasQuadrangle Γ c q)
    {P' T : Set V} (hF : IsFullSubquadrangle c P' q)
    (hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T) (hsub : T ⊆ P') :
    IsStarPlane (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P')
      {v : subquadrangleSet Γ c P' | (v : V) ∈ T} := by
  rw [isStarPlane_subquadrangle_iff hΓ hF]
  have hval : Subtype.val '' {v : subquadrangleSet Γ c P' | (v : V) ∈ T} = T := by
    ext a
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro ha
      exact ⟨⟨a, mem_subquadrangleSet.mpr (Or.inl (hsub ha))⟩, ha, rfl⟩
  rw [hval]
  exact hT
private theorem inter_nonempty_of_starPlane_subquadrangle (hΓ : IsThasQuadrangle Γ c q)
    {P' : Set V} (hF : IsFullSubquadrangle c P' q)
    {X Y : Set (subquadrangleSet Γ c P')}
    (hX : IsStarPlane (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X)
    (hY : IsStarPlane (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') Y) : (X ∩ Y).Nonempty := by
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hst : q ^ 2 ≠ q := by
    intro h
    have hq1 : 1 < q := by have := hΓ.two_le; omega
    have hlt : q < q ^ 2 := lt_self_pow₀ hq1 (by norm_num)
    omega
  exact inter_nonempty
    (isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hF)
    (isThick_subquadrangleGraph hP hT c hΓ.deg hF hΓ.two_le)
    (subquadrangleColoring c P') (degree_subquadrangleGraph hΓ hF)
    (fun w hw => isRegularVertex_subquadrangle hΓ hF w hw)
    hst (talliniCondPrime_subquadrangle hΓ hF) hX hY
private theorem inter_subset_of_mem_threeBundle (hΓ : IsThasQuadrangle Γ c q) {T : Set V}
    (hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T) {E F D : Set V}
    (hE : E ∈ threeBundle Γ c q T) (hF : F ∈ threeBundle Γ c q T) (hne : E ≠ F)
    (hD : D ∈ threeBundle Γ c q T) : E ∩ F ⊆ D := by
  rw [inter_eq_of_mem_threeBundle hΓ hT hE hF hne]
  exact hD.2
private theorem neighborSet_subset_of_mem_lineBundle (hΓ : IsThasQuadrangle Γ c q) {L : V}
    (hL : c L = 1) {D : Set V} (hD : D ∈ lineBundle Γ c L) : Γ.neighborSet L ⊆ D := by
  obtain ⟨x, hxL, rfl⟩ := hD
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hxL
  intro z hz
  have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL hz
  rw [mem_ptPerp]
  refine ⟨hz0, ?_⟩
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  rw [ha]
  by_cases hzx : z = x
  · rw [hzx]
    simp
  · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hΓ.gp hz.symm hxL hzx)
private theorem inter_subset_of_mem_lineBundle (hΓ : IsThasQuadrangle Γ c q) {L : V}
    (hL : c L = 1) {E F D : Set V} (hE : E ∈ lineBundle Γ c L) (hF : F ∈ lineBundle Γ c L)
    (hne : E ≠ F) (hD : D ∈ lineBundle Γ c L) : E ∩ F ⊆ D := by
  rw [inter_eq_of_mem_lineBundle hΓ hL hE hF hne]
  exact neighborSet_subset_of_mem_lineBundle hΓ hL hD
private theorem exists_traceSet_eq_of_subset_ptPerp (hΓ : IsThasQuadrangle Γ c q)
    {T : Set V} {y z x : V} (hy : c y = 0) (hyz : Γ.dist y z = 4)
    (hTeq : T = traceSet Γ y z) (hsub : T ⊆ ptPerp Γ c {x}) :
    ∃ z', c z' = 0 ∧ Γ.dist x z' = 4 ∧ T = traceSet Γ x z' := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hxspan : x ∈ spanSet Γ y z := by
    intro w hw
    have hwT : w ∈ T := by rw [hTeq]; exact hw
    have h := (mem_ptPerp.mp (hsub hwT)).2 x (by simp)
    rwa [SimpleGraph.dist_comm] at h
  have hx0 : c x = 0 := (color_eq_of_mem_span hP hT c hyz hxspan).trans hy
  have hcard : (spanSet Γ y z).ncard = q + 1 := hΓ.span y z hy hyz
  have h2 : 1 < (spanSet Γ y z).ncard := by
    rw [hcard]
    have h2q : 2 ≤ q := hΓ.two_le
    omega
  obtain ⟨z', hz'span, hz'ne⟩ := Set.exists_ne_of_one_lt_ncard h2 x
  have hxne : x ≠ z' := hz'ne.symm
  have hdist : Γ.dist x z' = 4 :=
    dist_eq_four_of_mem_span hP hT hyz hxspan hz'span hxne
  have hcolor : c z' = 0 := (color_eq_of_mem_span hP hT c hyz hz'span).trans hy
  have htrace : traceSet Γ x z' = traceSet Γ y z :=
    (span_eq_of_mem hP hT hyz hxspan hz'span hxne).2.2
  exact ⟨z', hcolor, hdist, hTeq.trans htrace.symm⟩
private theorem mem_conePlane_of_eq (hΓ : IsThasQuadrangle Γ c q) {T : Set V} {x₀ y₀ z : V}
    (hx₀ : c x₀ = 0) (hx₀y₀ : Γ.dist x₀ y₀ = 4) (hz : z ∈ traceSet Γ x₀ y₀)
    (hTeq : T = ptPerp Γ c {z} ∩ clSet Γ x₀ y₀) :
    x₀ ∈ T ∧ y₀ ∈ T ∧ z ∈ T := by
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP hx₀ hz.1
  have hx₀perp : x₀ ∈ ptPerp Γ c {z} := by
    rw [mem_ptPerp]
    refine ⟨hx₀, fun a ha => ?_⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact le_of_eq hz.1
  have hx₀cl : x₀ ∈ clSet Γ x₀ y₀ := ⟨x₀, left_mem_spanSet hx₀y₀, by simp⟩
  have hy₀perp : y₀ ∈ ptPerp Γ c {z} := by
    rw [mem_ptPerp]
    refine ⟨(color_eq_of_dist_four hP hx₀y₀).symm.trans hx₀, fun a ha => ?_⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact le_of_eq hz.2
  have hy₀cl : y₀ ∈ clSet Γ x₀ y₀ := ⟨y₀, right_mem_spanSet hx₀y₀, by simp⟩
  have hzperp : z ∈ ptPerp Γ c {z} := mem_ptPerp_self hz0
  have hzcl : z ∈ clSet Γ x₀ y₀ := by
    refine ⟨x₀, left_mem_spanSet hx₀y₀, ?_⟩
    have h := dist_eq_two_of_mem_span_of_mem_trace hP hT hx₀y₀
      (left_mem_spanSet hx₀y₀) hz
    rw [SimpleGraph.dist_comm]
    exact le_of_eq h
  exact ⟨by rw [hTeq]; exact ⟨hx₀perp, hx₀cl⟩,
    by rw [hTeq]; exact ⟨hy₀perp, hy₀cl⟩,
    by rw [hTeq]; exact ⟨hzperp, hzcl⟩⟩
private theorem mem_clSet_of_mem_traceSet (hΓ : IsThasQuadrangle Γ c q) {x x₀ y₀ : V}
    (hx₀y₀ : Γ.dist x₀ y₀ = 4) (hx : x ∈ traceSet Γ x₀ y₀) : x ∈ clSet Γ x₀ y₀ := by
  refine ⟨x₀, left_mem_spanSet hx₀y₀, ?_⟩
  have h := dist_eq_two_of_mem_span_of_mem_trace hΓ.gp hΓ.thick hx₀y₀
    (left_mem_spanSet hx₀y₀) hx
  rw [SimpleGraph.dist_comm]
  exact le_of_eq h
private theorem conePlane_vertex (hΓ : IsThasQuadrangle Γ c q) {T : Set V} {x x₀ y₀ z : V}
    (hx₀ : c x₀ = 0) (hx₀y₀ : Γ.dist x₀ y₀ = 4) (hz : z ∈ traceSet Γ x₀ y₀)
    (hTeq : T = ptPerp Γ c {z} ∩ clSet Γ x₀ y₀) (hsub : T ⊆ ptPerp Γ c {x}) :
    x ∈ traceSet Γ x₀ y₀ ∧ T = ptPerp Γ c {x} ∩ clSet Γ x₀ y₀ := by
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  obtain ⟨hx₀T, hy₀T, hzT⟩ := mem_conePlane_of_eq hΓ hx₀ hx₀y₀ hz hTeq
  have hx₀x : Γ.dist x₀ x ≤ 2 := (mem_ptPerp.mp (hsub hx₀T)).2 x (by simp)
  have hy₀x : Γ.dist y₀ x ≤ 2 := (mem_ptPerp.mp (hsub hy₀T)).2 x (by simp)
  have hzx : Γ.dist z x ≤ 2 := (mem_ptPerp.mp (hsub hzT)).2 x (by simp)
  have hy₀0 : c y₀ = 0 := (color_eq_of_dist_four hP hx₀y₀).symm.trans hx₀
  have hx0 : c x = 0 := color_zero_of_dist_le_two hΓ hx₀ hy₀0 hx₀y₀ hx₀x hy₀x
  have hxne₀ : x ≠ x₀ := by
    intro h
    rw [h, SimpleGraph.dist_comm, hx₀y₀] at hy₀x
    omega
  have hxne₁ : x ≠ y₀ := by
    intro h
    rw [h, hx₀y₀] at hx₀x
    omega
  have hx₀x2 : Γ.dist x₀ x = 2 := by
    have heven : Even (Γ.dist x₀ x) :=
      (hP.eq_iff_even_dist c x₀ x).1 (hx₀.trans hx0.symm)
    have hne0 : Γ.dist x₀ x ≠ 0 :=
      fun h0 => hxne₀ ((hP.connected.dist_eq_zero_iff).mp h0).symm
    obtain ⟨k, hk⟩ := heven
    omega
  have hy₀x2 : Γ.dist y₀ x = 2 := by
    have heven : Even (Γ.dist y₀ x) :=
      (hP.eq_iff_even_dist c y₀ x).1 (hy₀0.trans hx0.symm)
    have hne0 : Γ.dist y₀ x ≠ 0 :=
      fun h0 => hxne₁ ((hP.connected.dist_eq_zero_iff).mp h0).symm
    obtain ⟨k, hk⟩ := heven
    omega
  have hxtrace : x ∈ traceSet Γ x₀ y₀ := ⟨hx₀x2, hy₀x2⟩
  have hxz : x = z := by
    by_contra hne
    have h4 : Γ.dist x z = 4 :=
      dist_eq_four_of_mem_trace hP hx₀y₀ hxtrace hz hne
    rw [SimpleGraph.dist_comm] at hzx
    omega
  subst hxz
  exact ⟨hz, hTeq⟩
private theorem exists_mem_neighborSet_dist_eq_two (hΓ : IsThasQuadrangle Γ c q) {x z L : V}
    (hxz : Γ.dist x z = 4) (hL1 : c L = 1) (hLx : Γ.Adj L x) :
    ∃ p, Γ.Adj L p ∧ Γ.dist z p = 2 := by
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hLx
  have hz0 : c z = 0 := (color_eq_of_dist_four hP hxz).symm.trans hx0
  have hxz_ne : x ≠ z := by
    intro h
    rw [h, SimpleGraph.dist_self] at hxz
    omega
  have hzL : ¬ Γ.Adj z L := by
    intro hLz
    have h2 : Γ.dist x z = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hLx.symm hLz.symm hxz_ne
    omega
  have h3 : Γ.dist z L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hzL
      (by rw [hz0, hL1]; decide)
  exact ⟨proj hP h3, proj_adj hP h3, proj_dist hP h3⟩
private theorem exists_mem_traceSet_adj (hΓ : IsThasQuadrangle Γ c q) {x z s N : V}
    (hx : c x = 0) (hxz : Γ.dist x z = 4) (hs : s ∈ spanSet Γ x z) (hNs : Γ.Adj N s) :
    ∃ w, w ∈ traceSet Γ x z ∧ Γ.Adj N w := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hs0 : c s = 0 := (color_eq_of_mem_span hP hT c hxz hs).trans hx
  have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hs0 hNs.symm
  have hd : ∀ w ∈ traceSet Γ x z, Γ.dist w s = 2 := fun w hw => by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT hxz hs hw
  let f : V → V := fun w => if h : w ∈ traceSet Γ x z then commonNeighbor hP (hd w h) else s
  have hfinj : Set.InjOn f (traceSet Γ x z) := by
    intro u hu v hv heq
    by_contra huv
    have hu' : Γ.Adj u (f u) := by
      simp only [f, dif_pos hu]
      exact commonNeighbor_adj_left hP (hd u hu)
    have hv' : Γ.Adj v (f v) := by
      simp only [f, dif_pos hv]
      exact commonNeighbor_adj_left hP (hd v hv)
    have h4 : Γ.dist u v = 4 := dist_eq_four_of_mem_trace hP hxz hu hv huv
    have h2 : Γ.dist u v = 2 := by
      refine dist_eq_two_of_adj_of_adj_of_ne hP hu' ?_ huv
      rw [heq]
      exact hv'.symm
    omega
  have himage : f '' traceSet Γ x z ⊆ Γ.neighborSet s := by
    rintro y ⟨w, hw, rfl⟩
    simp only [f, dif_pos hw]
    exact commonNeighbor_adj_right hP (hd w hw)
  have hTcard : (traceSet Γ x z).ncard = q ^ 3 + 1 := by
    rw [ncard_trace hP hxz, hΓ.deg x, if_pos hx]
  have hNcard : (Γ.neighborSet s).ncard = q ^ 3 + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hΓ.deg s, if_pos hs0]
  have hcard : (f '' traceSet Γ x z).ncard = (Γ.neighborSet s).ncard := by
    rw [hfinj.ncard_image, hTcard, hNcard]
  have hset : f '' traceSet Γ x z = Γ.neighborSet s :=
    Set.eq_of_subset_of_ncard_le himage (by rw [hcard])
  have hNmem : N ∈ f '' traceSet Γ x z := by rw [hset]; exact hNs.symm
  obtain ⟨w, hw, hfw⟩ := hNmem
  refine ⟨w, hw, ?_⟩
  have hwadj : Γ.Adj w (f w) := by
    simp only [f, dif_pos hw]
    exact commonNeighbor_adj_left hP (hd w hw)
  rw [hfw] at hwadj
  exact hwadj.symm
private theorem inter_nonempty_traceSet_traceSet (hΓ : IsThasQuadrangle Γ c q) {x z z' : V}
    (hx : c x = 0) (hxz : Γ.dist x z = 4) (hxz' : Γ.dist x z' = 4) :
    (traceSet Γ x z ∩ traceSet Γ x z').Nonempty := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := (color_eq_of_dist_four hP hxz).symm.trans hx
  have hz'0 : c z' = 0 := (color_eq_of_dist_four hP hxz').symm.trans hx
  have hxz_ne : x ≠ z := by
    intro h
    rw [h, SimpleGraph.dist_self] at hxz
    omega
  have htrace : (traceSet Γ x z).Nonempty := by
    have hcard : (traceSet Γ x z).ncard = q ^ 3 + 1 := by
      rw [ncard_trace hP hxz, hΓ.deg x, if_pos hx]
    have hpos : 0 < (traceSet Γ x z).ncard := by rw [hcard]; omega
    exact (Set.ncard_pos (s := traceSet Γ x z)).mp hpos
  rcases eq_or_ne z z' with rfl | hzz'
  · obtain ⟨w, hw⟩ := htrace
    exact ⟨w, hw, hw⟩
  by_cases hspan : z' ∈ spanSet Γ x z
  · have hxne : x ≠ z' := by
      intro h
      rw [h, SimpleGraph.dist_self] at hxz'
      omega
    have heq : traceSet Γ x z' = traceSet Γ x z :=
      (span_eq_of_mem hP hT hxz (left_mem_spanSet hxz) hspan hxne).2.2
    obtain ⟨w, hw⟩ := htrace
    exact ⟨w, hw, by rw [heq]; exact hw⟩
  by_cases hcl : z' ∈ clSet Γ x z
  · obtain ⟨s, hs, hz's⟩ := hcl
    have hsne : s ≠ z' := fun h => hspan (h ▸ hs)
    have hs0 : c s = 0 := (color_eq_of_mem_span hP hT c hxz hs).trans hx
    have hz's2 : Γ.dist z' s = 2 := by
      have heven : Even (Γ.dist z' s) :=
        (hP.eq_iff_even_dist c z' s).1 (hz'0.trans hs0.symm)
      have hne0 : Γ.dist z' s ≠ 0 :=
        fun h0 => hsne ((hP.connected.dist_eq_zero_iff).mp h0).symm
      obtain ⟨k, hk⟩ := heven
      omega
    let N : V := commonNeighbor hP hz's2
    have hNs : Γ.Adj N s := (commonNeighbor_adj_right hP hz's2).symm
    obtain ⟨w, hwT, hwN⟩ := exists_mem_traceSet_adj hΓ hx hxz hs hNs
    have hz'N : Γ.Adj z' N := commonNeighbor_adj_left hP hz's2
    have hne : w ≠ z' := by
      intro h
      have h2 : Γ.dist x z' = 2 := by rw [← h]; exact hwT.1
      rw [hxz'] at h2
      omega
    have hwz' : Γ.dist w z' = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hwN.symm hz'N.symm hne
    exact ⟨w, hwT, ⟨hwT.1, by rw [SimpleGraph.dist_comm]; exact hwz'⟩⟩
  by_cases hzz'2 : Γ.dist z z' = 2
  · let M : V := commonNeighbor hP hzz'2
    have hMz : Γ.Adj z M := commonNeighbor_adj_left hP hzz'2
    have hMz' : Γ.Adj z' M := commonNeighbor_adj_right hP hzz'2
    have hM1 : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hz0 hMz
    have hxM : ¬ Γ.Adj x M := by
      intro hxM
      have h2 : Γ.dist x z = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hxM hMz.symm hxz_ne
      rw [hxz] at h2
      omega
    have hM3 : Γ.dist x M = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c hxM (by rw [hx, hM1]; decide)
    have hMp : Γ.Adj M (proj hP hM3) := proj_adj hP hM3
    have hxp : Γ.dist x (proj hP hM3) = 2 := proj_dist hP hM3
    have hzp : Γ.dist z (proj hP hM3) = 2 := by
      by_cases hzp : z = proj hP hM3
      · exfalso
        rw [hzp] at hxz
        omega
      · exact dist_eq_two_of_adj_of_adj_of_ne hP hMz hMp hzp
    have hz'p : Γ.dist z' (proj hP hM3) = 2 := by
      by_cases hz'p : z' = proj hP hM3
      · exfalso
        rw [hz'p] at hxz'
        omega
      · exact dist_eq_two_of_adj_of_adj_of_ne hP hMz' hMp hz'p
    exact ⟨proj hP hM3, ⟨hxp, hzp⟩, ⟨hxp, hz'p⟩⟩
  · have hzz'4 : Γ.dist z z' = 4 := by
      have heven : Even (Γ.dist z z') :=
        (hP.eq_iff_even_dist c z z').1 (hz0.trans hz'0.symm)
      have hle : Γ.dist z z' ≤ 4 := hP.dist_le (by norm_num) z z'
      have hne0 : Γ.dist z z' ≠ 0 :=
        fun h0 => hzz' ((hP.connected.dist_eq_zero_iff).mp h0)
      obtain ⟨k, hk⟩ := heven
      omega
    have hcard : (centreSet Γ x z z').ncard = q + 1 :=
      ncard_centreSet hΓ hx hxz hxz' hzz'4 hcl
    have hpos : 0 < (centreSet Γ x z z').ncard := by rw [hcard]; omega
    obtain ⟨w, hw⟩ := (Set.ncard_pos (s := centreSet Γ x z z')).mp hpos
    exact ⟨w, hw.1, ⟨hw.1.1, hw.2⟩⟩
private theorem inter_nonempty_of_traceSet_conePlane (hΓ : IsThasQuadrangle Γ c q)
    {x z x₀ y₀ : V} (hx : c x = 0) (hxz : Γ.dist x z = 4) (hx₀ : c x₀ = 0)
    (hx₀y₀ : Γ.dist x₀ y₀ = 4) (hxtrace : x ∈ traceSet Γ x₀ y₀) :
    (traceSet Γ x z ∩ (ptPerp Γ c {x} ∩ clSet Γ x₀ y₀)).Nonempty := by
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hx₀x : Γ.dist x₀ x = 2 := hxtrace.1
  let N : V := commonNeighbor hP hx₀x
  have hNx₀ : Γ.Adj x₀ N := commonNeighbor_adj_left hP hx₀x
  have hNx : Γ.Adj N x := (commonNeighbor_adj_right hP hx₀x).symm
  have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hx₀ hNx₀
  obtain ⟨p, hNp, hzp⟩ := exists_mem_neighborSet_dist_eq_two hΓ hxz hN1 hNx
  have hp0 : c p = 0 := color_eq_zero_of_adj_of_color_eq_one hN1 hNp
  have hpx : Γ.dist x p = 2 := by
    by_cases hxp : x = p
    · exfalso
      rw [hxp, SimpleGraph.dist_comm] at hxz
      omega
    · exact dist_eq_two_of_adj_of_adj_of_ne hP hNx.symm hNp hxp
  refine ⟨p, ⟨hpx, hzp⟩, ⟨?_, ?_⟩⟩
  · rw [mem_ptPerp]
    refine ⟨hp0, fun a ha => ?_⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [SimpleGraph.dist_comm]
    exact le_of_eq hpx
  · rw [mem_clSet]
    refine ⟨x₀, left_mem_spanSet hx₀y₀, ?_⟩
    by_cases hpx₀ : p = x₀
    · rw [hpx₀]; simp
    · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hNp.symm hNx₀.symm hpx₀)
private theorem inter_nonempty_of_traceSet_neighborSet (hΓ : IsThasQuadrangle Γ c q)
    {x z L : V} (hx : c x = 0) (hxz : Γ.dist x z = 4) (hL1 : c L = 1)
    (hLx : Γ.Adj L x) : (traceSet Γ x z ∩ Γ.neighborSet L).Nonempty := by
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  obtain ⟨p, hLp, hzp⟩ := exists_mem_neighborSet_dist_eq_two hΓ hxz hL1 hLx
  have hpx : Γ.dist x p = 2 := by
    by_cases hxp : x = p
    · exfalso
      rw [hxp, SimpleGraph.dist_comm] at hxz
      omega
    · exact dist_eq_two_of_adj_of_adj_of_ne hP hLx.symm hLp hxp
  exact ⟨p, ⟨⟨hpx, hzp⟩, hLp⟩⟩
private theorem inter_nonempty_of_planes_subset_threespace (hΓ : IsThasQuadrangle Γ c q)
    {E T T' : Set V} (hE : IsThreespace Γ c q E)
    (hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T)
    (hT' : IsTracePlane Γ c T' ∨ IsConePlane Γ c T') (hTE : T ⊆ E) (hT'E : T' ⊆ E) :
    (T ∩ T').Nonempty := by
  classical
  rcases hE with ⟨x, hx, rfl⟩ | hF'
  · rcases hT with ⟨y, z, hy, hyz, hTeq⟩ | ⟨x₀, y₀, z, hx₀, hx₀y₀, hz, hTeq⟩
    · obtain ⟨z₁, -, hxz₁, hTeq₁⟩ :=
        exists_traceSet_eq_of_subset_ptPerp hΓ hy hyz hTeq hTE
      rcases hT' with ⟨y', z', hy', hyz', hT'eq⟩ |
          ⟨x₀', y₀', z'', hx₀', hx₀'y₀', hz'', hT'eq⟩
      · obtain ⟨z₂, -, hxz₂, hT'eq₁⟩ :=
          exists_traceSet_eq_of_subset_ptPerp hΓ hy' hyz' hT'eq hT'E
        rw [hTeq₁, hT'eq₁]
        exact inter_nonempty_traceSet_traceSet hΓ hx hxz₁ hxz₂
      · obtain ⟨hxcone, hT'eq₁⟩ := conePlane_vertex hΓ hx₀' hx₀'y₀' hz'' hT'eq hT'E
        rw [hTeq₁, hT'eq₁]
        exact inter_nonempty_of_traceSet_conePlane hΓ hx hxz₁ hx₀' hx₀'y₀' hxcone
    · obtain ⟨hxcone, hTeq₁⟩ := conePlane_vertex hΓ hx₀ hx₀y₀ hz hTeq hTE
      rcases hT' with ⟨y', z', hy', hyz', hT'eq⟩ |
          ⟨x₀', y₀', z'', hx₀', hx₀'y₀', hz'', hT'eq⟩
      · obtain ⟨z₂, -, hxz₂, hT'eq₁⟩ :=
          exists_traceSet_eq_of_subset_ptPerp hΓ hy' hyz' hT'eq hT'E
        rw [hTeq₁, hT'eq₁]
        obtain ⟨w, hw1, hw2⟩ :=
          inter_nonempty_of_traceSet_conePlane hΓ hx hxz₂ hx₀ hx₀y₀ hxcone
        exact ⟨w, hw2, hw1⟩
      · obtain ⟨hxcone', hT'eq₁⟩ := conePlane_vertex hΓ hx₀' hx₀'y₀' hz'' hT'eq hT'E
        rw [hTeq₁, hT'eq₁]
        exact ⟨x, ⟨mem_ptPerp_self hx, mem_clSet_of_mem_traceSet hΓ hx₀y₀ hxcone⟩,
          ⟨mem_ptPerp_self hx, mem_clSet_of_mem_traceSet hΓ hx₀'y₀' hxcone'⟩⟩
  · have hX : IsStarPlane (Γ.induce (subquadrangleSet Γ c E)) (subquadrangleColoring c E)
        {v : subquadrangleSet Γ c E | (v : V) ∈ T} :=
      isStarPlane_subquadrangle_of_subset hΓ hF' hT hTE
    have hY : IsStarPlane (Γ.induce (subquadrangleSet Γ c E)) (subquadrangleColoring c E)
        {v : subquadrangleSet Γ c E | (v : V) ∈ T'} :=
      isStarPlane_subquadrangle_of_subset hΓ hF' hT' hT'E
    obtain ⟨v, hv⟩ := inter_nonempty_of_starPlane_subquadrangle hΓ hF' hX hY
    exact ⟨v.1, hv.1, hv.2⟩
private theorem inter_nonempty_of_plane_neighborSet (hΓ : IsThasQuadrangle Γ c q)
    {T : Set V} {y L : V} (hyL : Γ.Adj L y) (hL : c L = 1)
    (hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T) (hTperp : T ⊆ ptPerp Γ c {y}) :
    (T ∩ Γ.neighborSet L).Nonempty := by
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hL hyL
  rcases hT with ⟨a, z, ha, haz, hTeq⟩ | ⟨x₀, y₀, z, hx₀, hx₀y₀, hz, hTeq⟩
  · obtain ⟨z₁, -, hyz₁, hTeq₁⟩ :=
      exists_traceSet_eq_of_subset_ptPerp hΓ ha haz hTeq hTperp
    rw [hTeq₁]
    exact inter_nonempty_of_traceSet_neighborSet hΓ hy0 hyz₁ hL hyL
  · obtain ⟨hytrace, hTeq₁⟩ := conePlane_vertex hΓ hx₀ hx₀y₀ hz hTeq hTperp
    rw [hTeq₁]
    exact ⟨y, ⟨mem_ptPerp_self hy0, mem_clSet_of_mem_traceSet hΓ hx₀y₀ hytrace⟩, hyL⟩
private theorem inter_inter_inter_nonempty (hΓ : IsThasQuadrangle Γ c q)
    {β β' : Set (Set V)} (hβ : IsThreeBundle Γ c q β) (hβ' : IsThreeBundle Γ c q β')
    {E F G : Set V} (hEβ : E ∈ β) (hEβ' : E ∈ β') (hFβ : F ∈ β) (hFE : F ≠ E)
    (hGβ' : G ∈ β') (hGE : G ≠ E) : (E ∩ F ∩ G).Nonempty := by
  classical
  have hEthree : IsThreespace Γ c q E := isThreespace_of_mem_isThreeBundle hβ hEβ
  rcases hβ with ⟨T, hT, rfl⟩ | ⟨L, hL, rfl⟩
  · have hEFT : E ∩ F = T := inter_eq_of_mem_threeBundle hΓ hT hEβ hFβ (Ne.symm hFE)
    have hTE : T ⊆ E := by rw [← hEFT]; exact Set.inter_subset_left
    rcases hβ' with ⟨T', hT', rfl⟩ | ⟨L', hL', rfl⟩
    · have hEGT' : E ∩ G = T' :=
        inter_eq_of_mem_threeBundle hΓ hT' hEβ' hGβ' (Ne.symm hGE)
      have hT'E : T' ⊆ E := by rw [← hEGT']; exact Set.inter_subset_left
      obtain ⟨w, hwT, hwT'⟩ :=
        inter_nonempty_of_planes_subset_threespace hΓ hEthree hT hT' hTE hT'E
      exact ⟨w, by rw [hEFT]; exact hwT, hGβ'.2 hwT'⟩
    · obtain ⟨y, hyL', hEeq⟩ := hEβ'
      obtain ⟨w, hwT, hwNL'⟩ :=
        inter_nonempty_of_plane_neighborSet hΓ hyL' hL' hT (hEeq ▸ hTE)
      have hEGL' : E ∩ G = Γ.neighborSet L' :=
        inter_eq_of_mem_lineBundle hΓ hL' ⟨y, hyL', hEeq⟩ hGβ' (Ne.symm hGE)
      have hwG : w ∈ G := by
        have h : w ∈ E ∩ G := by rw [hEGL']; exact hwNL'
        exact h.2
      exact ⟨w, by rw [hEFT]; exact hwT, hwG⟩
  · have hEFL : E ∩ F = Γ.neighborSet L :=
      inter_eq_of_mem_lineBundle hΓ hL hEβ hFβ (Ne.symm hFE)
    rcases hβ' with ⟨T', hT', rfl⟩ | ⟨L', hL', rfl⟩
    · have hEGT' : E ∩ G = T' :=
        inter_eq_of_mem_threeBundle hΓ hT' hEβ' hGβ' (Ne.symm hGE)
      have hT'E : T' ⊆ E := by rw [← hEGT']; exact Set.inter_subset_left
      obtain ⟨y, hyL, hEeq⟩ := hEβ
      obtain ⟨w, hwT', hwNL⟩ :=
        inter_nonempty_of_plane_neighborSet hΓ hyL hL hT' (hEeq ▸ hT'E)
      have hwG : w ∈ G := by
        have h : w ∈ E ∩ G := by rw [hEGT']; exact hwT'
        exact h.2
      exact ⟨w, by rw [hEFL]; exact hwNL, hwG⟩
    · obtain ⟨y, hyL, hEeq⟩ := hEβ
      obtain ⟨y', hyL', hEeq'⟩ := hEβ'
      have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hL hyL
      have hy'0 : c y' = 0 := color_eq_zero_of_adj_of_color_eq_one hL' hyL'
      have hyy' : y = y' :=
        ptPerp_singleton_injective hΓ.gp hΓ.thick hy0 hy'0 (hEeq.symm.trans hEeq')
      have hEGL' : E ∩ G = Γ.neighborSet L' :=
        inter_eq_of_mem_lineBundle hΓ hL' ⟨y', hyL', hEeq'⟩ hGβ' (Ne.symm hGE)
      refine ⟨y, ?_, ?_⟩
      · rw [hEFL]; exact hyL
      · have hyN' : y ∈ Γ.neighborSet L' := hyy'.symm ▸ hyL'
        have h : y ∈ E ∩ G := by rw [hEGL']; exact hyN'
        exact h.2
private theorem exists_mem_all_of_isThreeBundle (hΓ : IsThasQuadrangle Γ c q)
    {β β' : Set (Set V)} (hβ : IsThreeBundle Γ c q β) (hβ' : IsThreeBundle Γ c q β')
    {E : Set V} (hEβ : E ∈ β) (hEβ' : E ∈ β') :
    ∃ w, c w = 0 ∧ (∀ D ∈ β, w ∈ D) ∧ ∀ D ∈ β', w ∈ D := by
  classical
  have hβcard : 1 < β.ncard := by
    rw [ncard_of_isThreeBundle hΓ hβ]
    have hq : 0 < q ^ 2 := pow_pos (by have := hΓ.two_le; omega) 2
    have h2 := hΓ.two_le
    omega
  obtain ⟨F, hFβ, hFE⟩ := Set.exists_ne_of_one_lt_ncard hβcard E
  have hβ'card : 1 < β'.ncard := by
    rw [ncard_of_isThreeBundle hΓ hβ']
    have hq : 0 < q ^ 2 := pow_pos (by have := hΓ.two_le; omega) 2
    have h2 := hΓ.two_le
    omega
  obtain ⟨G, hGβ', hGE⟩ := Set.exists_ne_of_one_lt_ncard hβ'card E
  obtain ⟨w, hwEFG⟩ :=
    inter_inter_inter_nonempty hΓ hβ hβ' hEβ hEβ' hFβ hFE hGβ' hGE
  have hwE : w ∈ E := hwEFG.1.1
  have hwF : w ∈ F := hwEFG.1.2
  have hwG : w ∈ G := hwEFG.2
  have hEthree : IsThreespace Γ c q E := isThreespace_of_mem_isThreeBundle hβ hEβ
  refine ⟨w, color_zero_of_mem_of_isThreespace hEthree hwE, ?_, ?_⟩
  · intro D hD
    rcases hβ with ⟨T, hT, rfl⟩ | ⟨L, hL, rfl⟩
    · exact inter_subset_of_mem_threeBundle hΓ hT hEβ hFβ (Ne.symm hFE) hD ⟨hwE, hwF⟩
    · exact inter_subset_of_mem_lineBundle hΓ hL hEβ hFβ (Ne.symm hFE) hD ⟨hwE, hwF⟩
  · intro D hD
    rcases hβ' with ⟨T, hT, rfl⟩ | ⟨L, hL, rfl⟩
    · exact inter_subset_of_mem_threeBundle hΓ hT hEβ' hGβ' (Ne.symm hGE) hD ⟨hwE, hwG⟩
    · exact inter_subset_of_mem_lineBundle hΓ hL hEβ' hGβ' (Ne.symm hGE) hD ⟨hwE, hwG⟩
private theorem exists_dist_eq_four (hΓ : IsThasQuadrangle Γ c q) {w : V} (hw : c w = 0) :
    ∃ z, Γ.dist w z = 4 := by
  classical
  have hcard : (Finset.univ.filter fun y => Γ.dist w y = 4).card = (q ^ 2) ^ 2 * q ^ 3 :=
    card_opposite hΓ.gp hΓ.thick c (s := q ^ 2) (t := q ^ 3) hΓ.deg hw
  have hq : 0 < q := by have := hΓ.two_le; omega
  have hpos : 0 < (Finset.univ.filter fun y => Γ.dist w y = 4).card := by
    rw [hcard]
    exact Nat.mul_pos (pow_pos (pow_pos hq 2) 2) (pow_pos hq 3)
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hz
  exact ⟨z, hz.2⟩
private theorem exists_fullSubquadrangle_notMem (hΓ : IsThasQuadrangle Γ c q) {w : V}
    (hw : c w = 0) : ∃ E' : Set V, IsFullSubquadrangle c E' q ∧ w ∉ E' := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  obtain ⟨z, hwz⟩ := exists_dist_eq_four hΓ hw
  have htrace : IsTracePlane Γ c (traceSet Γ w z) := ⟨w, z, hw, hwz, rfl⟩
  have hβ : IsThreeBundle Γ c q (threeBundle Γ c q (traceSet Γ w z)) :=
    Or.inl ⟨traceSet Γ w z, Or.inl htrace, rfl⟩
  have hβcard : (threeBundle Γ c q (traceSet Γ w z)).ncard = q ^ 2 + 1 :=
    ncard_of_isThreeBundle hΓ hβ
  have habs : {E | E ∈ threeBundle Γ c q (traceSet Γ w z) ∧
      ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}}.ncard = q + 1 :=
    ncard_abs_threeBundle hΓ htrace
  have hex : ∃ E ∈ threeBundle Γ c q (traceSet Γ w z),
      ¬ ∃ x, c x = 0 ∧ E = ptPerp Γ c {x} := by
    by_contra hall
    push Not at hall
    have hset : threeBundle Γ c q (traceSet Γ w z) =
        {E | E ∈ threeBundle Γ c q (traceSet Γ w z) ∧
          ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}} := by
      ext E
      exact ⟨fun hE => ⟨hE, hall E hE⟩, fun hE => hE.1⟩
    rw [hset] at hβcard
    have hq2 : q ^ 2 = q := by omega
    have hq1 : 1 < q := by have := hΓ.two_le; omega
    have hqpos : 0 < q := by omega
    have hlt : q < q * q := by
      calc q = q * 1 := (Nat.mul_one q).symm
        _ < q * q := Nat.mul_lt_mul_of_pos_left hq1 hqpos
    rw [pow_two] at hq2
    omega
  obtain ⟨E', hE'β, hE'nonabs⟩ := hex
  have hE'full : IsFullSubquadrangle c E' q := by
    rcases hE'β.1 with h | h
    · exact absurd h hE'nonabs
    · exact h
  refine ⟨E', hE'full, ?_⟩
  intro hwE'
  have hwT : w ∉ traceSet Γ w z := by
    have hdisj := spanSet_disjoint_traceSet hP hΓ.thick hwz
    exact fun h => Set.disjoint_left.mp hdisj (left_mem_spanSet hwz) h
  have hperp : IsThreespace Γ c q (ptPerp Γ c {w}) := Or.inl ⟨w, hw, rfl⟩
  have hTperp : traceSet Γ w z ⊆ ptPerp Γ c {w} := by
    intro a ha
    rw [mem_ptPerp]
    refine ⟨color_eq_zero_of_dist_eq_two hP hw ha.1, fun b hb => ?_⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    rw [SimpleGraph.dist_comm]
    exact le_of_eq ha.1
  have huniq := existsUnique_threespace hΓ (Or.inl htrace) hw hwT
  have heq : E' = ptPerp Γ c {w} :=
    huniq.unique ⟨hE'β.1, hE'β.2, hwE'⟩ ⟨hperp, hTperp, mem_ptPerp_self hw⟩
  exact hE'nonabs ⟨w, hw, heq⟩
theorem threeBundle_veblen (hΓ : IsThasQuadrangle Γ c q) {β β' γ₁ γ₂ : Set (Set V)}
    (hβ : IsThreeBundle Γ c q β) (hβ' : IsThreeBundle Γ c q β')
    (hγ₁ : IsThreeBundle Γ c q γ₁) (hγ₂ : IsThreeBundle Γ c q γ₂) (hββ' : (β ∩ β').Nonempty)
    {E₁ E₂ E₁' E₂' : Set V} (h1 : E₁ ∈ β) (h2 : E₂ ∈ β) (h1' : E₁' ∈ β') (h2' : E₂' ∈ β')
    (hne1 : E₁ ≠ E₁') (hne2 : E₂ ≠ E₂') (hγ1 : E₁ ∈ γ₁ ∧ E₁' ∈ γ₁)
    (hγ2 : E₂ ∈ γ₂ ∧ E₂' ∈ γ₂) : (γ₁ ∩ γ₂).Nonempty := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  obtain ⟨E, hEβ, hEβ'⟩ := hββ'
  obtain ⟨w, hw0, hwβ, hwβ'⟩ := exists_mem_all_of_isThreeBundle hΓ hβ hβ' hEβ hEβ'
  have hwγ₁ : ∀ D ∈ γ₁, w ∈ D := by
    have hw1 : w ∈ E₁ ∩ E₁' := ⟨hwβ E₁ h1, hwβ' E₁' h1'⟩
    rcases hγ₁ with ⟨T, hT, rfl⟩ | ⟨L, hL, rfl⟩
    · exact fun D hD => inter_subset_of_mem_threeBundle hΓ hT hγ1.1 hγ1.2 hne1 hD hw1
    · exact fun D hD => inter_subset_of_mem_lineBundle hΓ hL hγ1.1 hγ1.2 hne1 hD hw1
  have hwγ₂ : ∀ D ∈ γ₂, w ∈ D := by
    have hw2 : w ∈ E₂ ∩ E₂' := ⟨hwβ E₂ h2, hwβ' E₂' h2'⟩
    rcases hγ₂ with ⟨T, hT, rfl⟩ | ⟨L, hL, rfl⟩
    · exact fun D hD => inter_subset_of_mem_threeBundle hΓ hT hγ2.1 hγ2.2 hne2 hD hw2
    · exact fun D hD => inter_subset_of_mem_lineBundle hΓ hL hγ2.1 hγ2.2 hne2 hD hw2
  obtain ⟨E', hF', hwE'⟩ := exists_fullSubquadrangle_notMem hΓ hw0
  have hE'β : E' ∉ β := fun h => hwE' (hwβ E' h)
  have hE'β' : E' ∉ β' := fun h => hwE' (hwβ' E' h)
  have hE'γ₁ : E' ∉ γ₁ := fun h => hwE' (hwγ₁ E' h)
  have hE'γ₂ : E' ∉ γ₂ := fun h => hwE' (hwγ₂ E' h)
  obtain ⟨hβimg, -⟩ := isPlaneBundle_image hΓ hβ hF' hE'β
  obtain ⟨hβ'img, -⟩ := isPlaneBundle_image hΓ hβ' hF' hE'β'
  obtain ⟨hγ₁img, hinjγ₁⟩ := isPlaneBundle_image hΓ hγ₁ hF' hE'γ₁
  obtain ⟨hγ₂img, hinjγ₂⟩ := isPlaneBundle_image hΓ hγ₂ hF' hE'γ₂
  have hP'gp : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c E')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hΓ.thick c hΓ.deg hF'
  have hP'thick : IsThick (Γ.induce (subquadrangleSet Γ c E')) :=
    isThick_subquadrangleGraph hP hΓ.thick c hΓ.deg hF' hΓ.two_le
  have hdeg' : ∀ v : subquadrangleSet Γ c E',
      (Γ.induce (subquadrangleSet Γ c E')).degree v =
        if subquadrangleColoring c E' v = 0 then q + 1 else q ^ 2 + 1 :=
    fun v => degree_subquadrangleGraph hΓ hF' v
  have hreg' : ∀ v : subquadrangleSet Γ c E', subquadrangleColoring c E' v = 0 →
      IsRegularVertex (Γ.induce (subquadrangleSet Γ c E')) v :=
    fun v hv => isRegularVertex_subquadrangle hΓ hF' v hv
  have hst : q ^ 2 ≠ q := by
    intro h
    have hq1 : 1 < q := by have := hΓ.two_le; omega
    have hlt : q < q ^ 2 := lt_self_pow₀ hq1 (by norm_num)
    omega
  have hveblen : (((fun E'' => {v : subquadrangleSet Γ c E' | (v : V) ∈ E''}) '' γ₁) ∩
      ((fun E'' => {v : subquadrangleSet Γ c E' | (v : V) ∈ E''}) '' γ₂)).Nonempty :=
    bundle_veblen hP'gp hP'thick (subquadrangleColoring c E') hdeg' hreg'
      hst (talliniCond_subquadrangle hΓ hF') hβimg hβ'img hγ₁img hγ₂img
      ⟨(fun E'' => {v : subquadrangleSet Γ c E' | (v : V) ∈ E''}) E,
        ⟨⟨E, hEβ, rfl⟩, ⟨E, hEβ', rfl⟩⟩⟩
      ⟨E₁, h1, rfl⟩ ⟨E₂, h2, rfl⟩ ⟨E₁', h1', rfl⟩ ⟨E₂', h2', rfl⟩
      (fun h => hne1 (hinjγ₁ hγ1.1 hγ1.2 h))
      (fun h => hne2 (hinjγ₂ hγ2.1 hγ2.2 h))
      ⟨⟨E₁, hγ1.1, rfl⟩, ⟨E₁', hγ1.2, rfl⟩⟩
      ⟨⟨E₂, hγ2.1, rfl⟩, ⟨E₂', hγ2.2, rfl⟩⟩
  obtain ⟨π₃, hπ₃γ₁, hπ₃γ₂⟩ := hveblen
  obtain ⟨E₃, hE₃γ₁, hφE₃⟩ := hπ₃γ₁
  obtain ⟨E₃', hE₃'γ₂, hφE₃'⟩ := hπ₃γ₂
  have hπ₃γ₁' : π₃ ∈ (fun E'' => {v : subquadrangleSet Γ c E' | (v : V) ∈ E''}) '' γ₁ :=
    ⟨E₃, hE₃γ₁, hφE₃⟩
  have hE₃three : IsThreespace Γ c q E₃ := isThreespace_of_mem_isThreeBundle hγ₁ hE₃γ₁
  have hE₃'three : IsThreespace Γ c q E₃' := isThreespace_of_mem_isThreeBundle hγ₂ hE₃'γ₂
  have hval : Subtype.val '' π₃ = E₃ ∩ E' := by
    rw [← hφE₃]
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv0 : c (v : V) = 0 := color_zero_of_mem_of_isThreespace hE₃three hv
      refine ⟨hv, ?_⟩
      rcases mem_subquadrangleSet.mp v.2 with hv' | ⟨hv1, -⟩
      · exact hv'
      · rw [hv0] at hv1
        exact absurd hv1 (by decide)
    · rintro ⟨hzE₃, hzE'⟩
      exact ⟨⟨z, mem_subquadrangleSet.mpr (Or.inl hzE')⟩, hzE₃, rfl⟩
  have hval' : Subtype.val '' π₃ = E₃' ∩ E' := by
    rw [← hφE₃']
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv0 : c (v : V) = 0 := color_zero_of_mem_of_isThreespace hE₃'three hv
      refine ⟨hv, ?_⟩
      rcases mem_subquadrangleSet.mp v.2 with hv' | ⟨hv1, -⟩
      · exact hv'
      · rw [hv0] at hv1
        exact absurd hv1 (by decide)
    · rintro ⟨hzE₃, hzE'⟩
      exact ⟨⟨z, mem_subquadrangleSet.mpr (Or.inl hzE')⟩, hzE₃, rfl⟩
  have hstar : IsStarPlane (Γ.induce (subquadrangleSet Γ c E'))
      (subquadrangleColoring c E') π₃ := by
    rcases hγ₁img with ⟨L, -, heq⟩ | ⟨Y, y, -, -, heq⟩
    · rw [heq] at hπ₃γ₁'
      exact hπ₃γ₁'.1
    · rw [heq] at hπ₃γ₁'
      exact hπ₃γ₁'.1
  have hplane : IsTracePlane Γ c (Subtype.val '' π₃) ∨
      IsConePlane Γ c (Subtype.val '' π₃) :=
    (isStarPlane_subquadrangle_iff hΓ hF').mp hstar
  have hwT : w ∉ Subtype.val '' π₃ := by
    rw [hval]
    exact fun h => hwE' h.2
  have huniq := existsUnique_threespace hΓ hplane hw0 hwT
  have hsub₃ : Subtype.val '' π₃ ⊆ E₃ := by
    rw [hval]
    exact Set.inter_subset_left
  have hsub₃' : Subtype.val '' π₃ ⊆ E₃' := by
    rw [hval']
    exact Set.inter_subset_left
  have heq : E₃ = E₃' :=
    huniq.unique ⟨hE₃three, hsub₃, hwγ₁ E₃ hE₃γ₁⟩
      ⟨hE₃'three, hsub₃', hwγ₂ E₃' hE₃'γ₂⟩
  refine ⟨E₃, hE₃γ₁, ?_⟩
  rw [heq]
  exact hE₃'γ₂
end CFSG.Geometry.GeneralizedQuadrangles
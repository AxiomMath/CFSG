module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Intersections

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

private theorem ncard_cone_le (hΓ : IsThasQuadrangle Γ c q) {x y z : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) (hz : z ∈ traceSet Γ x y) :
    (ptPerp Γ c {z} ∩ clSet Γ x y).ncard ≤ (q + 1) * (q ^ 2 + 1) + 1 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP hx hz.1
  have hspan : (spanSet Γ x y).ncard = q + 1 := hΓ.span x y hx hxy
  let S : Finset V := Finset.univ.filter fun w => w ∈ spanSet Γ x y
  have hScoe : (↑S : Set V) = spanSet Γ x y := by
    ext w
    simp [S]
  have hScard : S.card = q + 1 := by
    rw [← Set.ncard_coe_finset S, hScoe, hspan]
  have hzw_of_mem : ∀ w ∈ spanSet Γ x y, Γ.dist z w = 2 := by
    intro w hw
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hw hz
  let Lf : V → V := fun w =>
    if h : w ∈ spanSet Γ x y then commonNeighbor hP (hzw_of_mem w h) else z
  have hLf_of_mem : ∀ w (h : w ∈ spanSet Γ x y), Lf w = commonNeighbor hP (hzw_of_mem w h) := by
    intro w hw
    show (if h : w ∈ spanSet Γ x y then commonNeighbor hP (hzw_of_mem w h) else z) = _
    rw [dif_pos hw]
  have hcover : ptPerp Γ c {z} ∩ clSet Γ x y ⊆
      ({z} : Set V) ∪ ↑(S.biUnion fun w => Γ.neighborFinset (Lf w)) := by
    intro p hp
    obtain ⟨hpz, hpcl⟩ := hp
    rw [mem_ptPerp] at hpz
    obtain ⟨hp0, hpzle⟩ := hpz
    rw [mem_clSet] at hpcl
    by_cases hpeq : p = z
    · exact Set.mem_union_left _ hpeq
    · refine Set.mem_union_right _ ?_
      rw [Finset.mem_coe, Finset.mem_biUnion]
      obtain ⟨w, hwspan, hpwle⟩ := hpcl
      refine ⟨w, ?_, ?_⟩
      · rw [← Finset.mem_coe, hScoe]
        exact hwspan
      · rw [mem_neighborFinset]
        rw [hLf_of_mem w hwspan]
        by_cases hpw : p = w
        · rw [hpw]
          exact (commonNeighbor_adj_right hP (hzw_of_mem w hwspan)).symm
        · have hw0 : c w = 0 := color_eq_zero_of_mem_span hP hT hx hxy hwspan
          have hpw2 : Γ.dist p w = 2 := dist_eq_two_of_le_two_of_ne hP hp0 hw0 hpw hpwle
          have hzp2 : Γ.dist z p = 2 :=
            dist_eq_two_of_le_two_of_ne hP hz0 hp0 (Ne.symm hpeq) (by
              rw [SimpleGraph.dist_comm]
              exact hpzle z (Set.mem_singleton z))
          obtain ⟨u, ⟨hzu, hpu, hwu⟩, -⟩ :=
            existsUnique_commonNeighbor_of_pairwise_dist_two hP hzp2
              (hzw_of_mem w hwspan) hpw2
          have hucn : u = commonNeighbor hP (hzw_of_mem w hwspan) :=
            eq_commonNeighbor hP (hzw_of_mem w hwspan) hzu hwu
          rw [hucn] at hpu
          exact hpu.symm
  have hline_card : ∀ w ∈ S, (Γ.neighborFinset (Lf w)).card = q ^ 2 + 1 := by
    intro w hw
    have hwspan : w ∈ spanSet Γ x y := by
      rw [← hScoe]
      exact hw
    rw [card_neighborFinset_eq_degree]
    have hLw : Lf w = commonNeighbor hP (hzw_of_mem w hwspan) := hLf_of_mem w hwspan
    have hL1 : c (Lf w) = 1 := by
      rw [hLw]
      exact color_eq_one_of_adj_of_color_eq_zero hz0
        (commonNeighbor_adj_left hP (hzw_of_mem w hwspan))
    rw [hΓ.deg (Lf w), if_neg (by rw [hL1]; decide)]
  calc (ptPerp Γ c {z} ∩ clSet Γ x y).ncard
      ≤ (({z} : Set V) ∪ ↑(S.biUnion fun w => Γ.neighborFinset (Lf w))).ncard :=
        Set.ncard_le_ncard hcover
    _ ≤ ({z} : Set V).ncard
          + (↑(S.biUnion fun w => Γ.neighborFinset (Lf w)) : Set V).ncard :=
        Set.ncard_union_le _ _
    _ = 1 + (S.biUnion fun w => Γ.neighborFinset (Lf w)).card := by
        rw [Set.ncard_singleton, Set.ncard_coe_finset]
    _ ≤ 1 + ∑ w ∈ S, (Γ.neighborFinset (Lf w)).card := by
        have h := Finset.card_biUnion_le (s := S)
          (t := fun w => Γ.neighborFinset (Lf w))
        omega
    _ = 1 + ∑ w ∈ S, (q ^ 2 + 1) := by
        congr 1
        exact Finset.sum_congr rfl hline_card
    _ = (q + 1) * (q ^ 2 + 1) + 1 := by
        rw [Finset.sum_const, smul_eq_mul, hScard]
        ring

private theorem ncard_lt_of_isFullSubquadrangle_of_trace_or_cone
    (hΓ : IsThasQuadrangle Γ c q) {E T : Set V} (hE : IsFullSubquadrangle c E q)
    (hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T) : T.ncard < E.ncard := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hEcard : E.ncard = (q ^ 2 + 1) * (q ^ 3 + 1) := by
    have h := ncard_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg (t' := q) hE
    rw [h]
    ring_nf
  have hTle : T.ncard ≤ (q + 1) * (q ^ 2 + 1) + 1 := by
    rcases hT with ⟨y, z, hy0, hyz, rfl⟩ | ⟨x, y, z, hx0, hxy, hz, rfl⟩
    · rw [ncard_trace hP hyz, hΓ.deg y, if_pos hy0]
      have hq' : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hΓ.two_le
      rw [← Nat.cast_le (α := ℤ)]
      push_cast
      nlinarith
    · exact ncard_cone_le hΓ hx0 hxy hz
  have hlt : (q + 1) * (q ^ 2 + 1) + 1 < (q ^ 2 + 1) * (q ^ 3 + 1) := by
    have hq := hΓ.two_le
    have h1 : q + 1 < q ^ 3 := by
      have h2 : 2 * q ≤ q * q := by
        rw [mul_comm 2 q]
        exact Nat.mul_le_mul_left q hq
      have h3 : q * q * 2 ≤ q * q * q := Nat.mul_le_mul_left (q * q) hq
      have hq3 : q ^ 3 = q * q * q := by ring
      rw [hq3]
      omega
    have h2 : (q + 1) * (q ^ 2 + 1) + 1 ≤ q ^ 3 * (q ^ 2 + 1) := by
      have hlt : (q + 1) * (q ^ 2 + 1) < q ^ 3 * (q ^ 2 + 1) :=
        Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      exact Nat.succ_le_of_lt hlt
    have h3 : q ^ 3 * (q ^ 2 + 1) < (q ^ 2 + 1) * (q ^ 3 + 1) := by
      calc q ^ 3 * (q ^ 2 + 1) = (q ^ 2 + 1) * q ^ 3 := by ring
        _ < (q ^ 2 + 1) * q ^ 3 + (q ^ 2 + 1) := Nat.lt_add_of_pos_right (by positivity)
        _ = (q ^ 2 + 1) * (q ^ 3 + 1) := by ring
    exact lt_of_le_of_lt h2 h3
  omega

private theorem threeBundle_case (hΓ : IsThasQuadrangle Γ c q) {T : Set V}
    (hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T) {E : Set V}
    (hE : IsFullSubquadrangle c E q) (hEβ : E ∉ threeBundle Γ c q T) :
    IsPlaneBundle (Γ.induce (subquadrangleSet Γ c E)) (subquadrangleColoring c E)
        ((fun E' => {v : subquadrangleSet Γ c E | (v : V) ∈ E'}) '' threeBundle Γ c q T) ∧
      Set.InjOn (fun E' => {v : subquadrangleSet Γ c E | (v : V) ∈ E'})
        (threeBundle Γ c q T) := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hTq : IsThick Γ := hΓ.thick
  let S : Set V := subquadrangleSet Γ c E
  let c' : (Γ.induce S).Coloring (Fin 2) := subquadrangleColoring c E
  let φ : Set V → Set (subquadrangleSet Γ c E) := fun E' => {v | (v : V) ∈ E'}
  have hP' : IsGeneralizedPolygon (Γ.induce S) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hTq c hΓ.deg hE
  have hT' : IsThick (Γ.induce S) :=
    isThick_subquadrangleGraph hP hTq c hΓ.deg hE hΓ.two_le
  have hdeg' : ∀ v : subquadrangleSet Γ c E, (Γ.induce S).degree v =
      if c' v = 0 then q + 1 else q ^ 2 + 1 := fun v => degree_subquadrangleGraph hΓ hE v
  have hreg' : ∀ v : subquadrangleSet Γ c E, c' v = 0 →
      IsRegularVertex (Γ.induce S) v := fun v hv => isRegularVertex_subquadrangle hΓ hE v hv
  have hii' : TalliniCondPrime (Γ.induce S) c' := talliniCondPrime_subquadrangle hΓ hE
  have hst' : q ^ 2 ≠ q := by
    have hq := hΓ.two_le
    have h1 : q < q ^ 2 := by
      have h2 : q * 1 < q * q := Nat.mul_lt_mul_of_pos_left hq (by omega)
      have hq2 : q ^ 2 = q * q := by ring
      simpa [hq2] using h2
    omega
  have hinj : Set.InjOn φ (threeBundle Γ c q T) := by
    intro E' hE' E'' hE'' heq
    by_contra hne
    have hneE' : E ≠ E' := by
      intro h
      exact hEβ (by rw [h]; exact hE')
    have hstar' : IsStarPlane (Γ.induce S) c' (φ E') :=
      isStarPlane_inter hΓ hE hE'.1 hneE'
    have hb : E' ∩ E'' = T := inter_eq_of_mem_threeBundle hΓ hT hE' hE'' hne
    have hphi : φ E' ∩ φ E'' = φ T := by
      rw [← hb]
      ext v
      simp [φ]
    have hPT : φ T = φ E' := by
      rw [← hphi, heq]
      exact Set.inter_self _
    have hstarT : IsStarPlane (Γ.induce S) c' (φ T) := hPT ▸ hstar'
    have hall : ∀ E3 ∈ threeBundle Γ c q T, φ E3 = φ T := by
      intro E3 hE3
      by_cases hEq : E3 = E'
      · rw [hEq, hPT]
      · have hb' : E3 ∩ E' = T := inter_eq_of_mem_threeBundle hΓ hT hE3 hE' hEq
        have hphi' : φ E3 ∩ φ E' = φ T := by
          rw [← hb']
          ext v
          simp [φ]
        have hsub : φ T ⊆ φ E3 := by
          intro v hv
          have hv' : v ∈ φ E3 ∩ φ E' := by
            rw [hphi']
            exact hv
          exact hv'.1
        have hstar3 : IsStarPlane (Γ.induce S) c' (φ E3) := by
          refine isStarPlane_inter hΓ hE hE3.1 ?_
          intro h
          exact hEβ (by rw [h]; exact hE3)
        obtain ⟨x, hx, y, hy, z, hz, hnc⟩ := hstarT.2
        exact eq_of_isStarPlane hP' hT' c' hdeg' hreg' hstar3 hstarT
          ⟨hsub hx, hx⟩ ⟨hsub hy, hy⟩ ⟨hsub hz, hz⟩ hnc
    have hTE : T.ncard < E.ncard :=
      ncard_lt_of_isFullSubquadrangle_of_trace_or_cone hΓ hE hT
    have hnotsub : ¬ E ⊆ T := by
      intro hsub
      have := Set.ncard_le_ncard hsub
      omega
    obtain ⟨p, hpE, hpT⟩ := Set.not_subset.mp hnotsub
    have hp0 : c p = 0 := hE.1 p hpE
    obtain ⟨Ep, ⟨hEpsp, hTsub, hpEp⟩, -⟩ := existsUnique_threespace hΓ hT hp0 hpT
    have hEpβ : Ep ∈ threeBundle Γ c q T := ⟨hEpsp, hTsub⟩
    have hφEp : φ Ep = φ T := hall Ep hEpβ
    have hmem : (⟨p, mem_subquadrangleSet.mpr (Or.inl hpE)⟩ :
        subquadrangleSet Γ c E) ∈ φ Ep := hpEp
    rw [hφEp] at hmem
    exact hpT hmem
  refine ⟨?_, hinj⟩
  have hFcard : (φ '' threeBundle Γ c q T).ncard = q ^ 2 + 1 := by
    rw [hinj.ncard_image, ncard_of_isThreeBundle hΓ (Or.inl ⟨T, hT, rfl⟩)]
  have hstarF : ∀ X ∈ φ '' threeBundle Γ c q T, IsStarPlane (Γ.induce S) c' X := by
    rintro X ⟨E', hE', rfl⟩
    refine isStarPlane_inter hΓ hE hE'.1 ?_
    intro h
    exact hEβ (by rw [h]; exact hE')
  have hpair : ∀ X ∈ φ '' threeBundle Γ c q T, ∀ Y ∈ φ '' threeBundle Γ c q T,
      X ≠ Y → X ∩ Y = φ T := by
    rintro X ⟨E', hE', rfl⟩ Y ⟨E'', hE'', rfl⟩ hXY
    have hne : E' ≠ E'' := by
      intro h
      exact hXY (by rw [h])
    have hb : E' ∩ E'' = T := inter_eq_of_mem_threeBundle hΓ hT hE' hE'' hne
    rw [← hb]
    ext v
    simp [φ]
  have h2 : 1 < (φ '' threeBundle Γ c q T).ncard := by
    rw [hFcard]
    have hq2 : 0 < q ^ 2 := pow_pos (by have hq := hΓ.two_le; omega) 2
    omega
  obtain ⟨X0, hX0, Y0, hY0, hX0Y0⟩ :=
    (Set.one_lt_ncard (s := φ '' threeBundle Γ c q T)).mp h2
  have hI : X0 ∩ Y0 = φ T := hpair X0 hX0 Y0 hY0 hX0Y0
  rcases inter_cases hP' hT' c' hdeg' hreg' (hstarF X0 hX0) (hstarF Y0 hY0) hX0Y0 with
    hemp | ⟨x, hx⟩ | hline
  · have hne := inter_nonempty hP' hT' c' hdeg' hreg' hst' hii'
      (hstarF X0 hX0) (hstarF Y0 hY0)
    rw [hemp] at hne
    exact absurd hne (by simp)
  · have hpairx : ∀ X ∈ φ '' threeBundle Γ c q T, ∀ Y ∈ φ '' threeBundle Γ c q T,
        X ≠ Y → X ∩ Y = {x} := by
      intro X hX Y hY hXY
      rw [hpair X hX Y hY hXY, ← hI]
      exact hx
    obtain ⟨X, hX, hXnon, hFeq⟩ := eq_tangentBundle_of_pairwise hP' hT' c' hdeg' hreg'
      hst' hii' hstarF hFcard hpairx
    have hxX : x ∈ X := by
      obtain ⟨Y, hY, hYX⟩ := Set.exists_ne_of_one_lt_ncard h2 X
      have hXY : X ≠ Y := fun h => hYX h.symm
      have hinter : X ∩ Y = {x} := hpairx X hX Y hY hXY
      have hxint : x ∈ X ∩ Y := by rw [hinter]; exact Set.mem_singleton x
      exact hxint.1
    exact Or.inr ⟨X, x, hXnon, hxX, hFeq⟩
  · have hline' : IsStarLine (Γ.induce S) c' (φ T) := by
      rw [← hI]
      exact hline
    exact Or.inl ⟨φ T, hline',
      eq_axisBundle_of_pairwise hP' hT' c' hdeg' hreg' hst' hii'
        hline' hstarF hFcard hpair⟩

private theorem lineBundle_case (hΓ : IsThasQuadrangle Γ c q) {L : V} (hL : c L = 1)
    {E : Set V} (hE : IsFullSubquadrangle c E q) (hEβ : E ∉ lineBundle Γ c L) :
    IsPlaneBundle (Γ.induce (subquadrangleSet Γ c E)) (subquadrangleColoring c E)
        ((fun E' => {v : subquadrangleSet Γ c E | (v : V) ∈ E'}) '' lineBundle Γ c L) ∧
      Set.InjOn (fun E' => {v : subquadrangleSet Γ c E | (v : V) ∈ E'}) (lineBundle Γ c L) := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hTq : IsThick Γ := hΓ.thick
  let S : Set V := subquadrangleSet Γ c E
  let c' : (Γ.induce S).Coloring (Fin 2) := subquadrangleColoring c E
  let φ : Set V → Set (subquadrangleSet Γ c E) := fun E' => {v | (v : V) ∈ E'}
  have hP' : IsGeneralizedPolygon (Γ.induce S) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hTq c hΓ.deg hE
  have hT' : IsThick (Γ.induce S) :=
    isThick_subquadrangleGraph hP hTq c hΓ.deg hE hΓ.two_le
  have hdeg' : ∀ v : subquadrangleSet Γ c E, (Γ.induce S).degree v =
      if c' v = 0 then q + 1 else q ^ 2 + 1 := fun v => degree_subquadrangleGraph hΓ hE v
  have hreg' : ∀ v : subquadrangleSet Γ c E, c' v = 0 →
      IsRegularVertex (Γ.induce S) v := fun v hv => isRegularVertex_subquadrangle hΓ hE v hv
  have hii' : TalliniCondPrime (Γ.induce S) c' := talliniCondPrime_subquadrangle hΓ hE
  have hst' : q ^ 2 ≠ q := by
    have hq := hΓ.two_le
    have h1 : q < q ^ 2 := by
      have h2 : q * 1 < q * q := Nat.mul_lt_mul_of_pos_left hq (by omega)
      have hq2 : q ^ 2 = q * q := by ring
      simpa [hq2] using h2
    omega
  have hvalM : Subtype.val '' φ (Γ.neighborSet L) = Γ.neighborSet L ∩ E := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : (u : V) ∈ Γ.neighborSet L := hu
      refine ⟨hu', ?_⟩
      have huL : Γ.Adj L (u : V) := by
        rwa [SimpleGraph.mem_neighborSet] at hu'
      have hu0 : c (u : V) = 0 := color_eq_zero_of_adj_of_color_eq_one hL huL
      rcases mem_subquadrangleSet.mp u.2 with h | ⟨h1, -⟩
      · exact h
      · rw [h1] at hu0
        exact absurd hu0 (by decide)
    · rintro ⟨hvL, hvE⟩
      exact ⟨⟨v, mem_subquadrangleSet.mpr (Or.inl hvE)⟩, hvL, rfl⟩
  have hinj : Set.InjOn φ (lineBundle Γ c L) := by
    rintro E' ⟨x, hxL, rfl⟩ E'' ⟨y, hyL, rfl⟩ heq
    by_contra hxy
    have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hxL
    have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hL hyL
    have hxy' : x ≠ y := fun h => hxy (by rw [h])
    have hne : ptPerp Γ c {x} ≠ ptPerp Γ c {y} := by
      intro h
      exact hxy' (ptPerp_singleton_injective hP hTq hx0 hy0 h)
    have hb : ptPerp Γ c {x} ∩ ptPerp Γ c {y} = Γ.neighborSet L :=
      inter_eq_of_mem_lineBundle hΓ hL ⟨x, hxL, rfl⟩ ⟨y, hyL, rfl⟩ hne
    have hphi : φ (ptPerp Γ c {x}) ∩ φ (ptPerp Γ c {y}) = φ (Γ.neighborSet L) := by
      rw [← hb]
      ext v
      simp [φ]
    have hXM : φ (ptPerp Γ c {x}) = φ (Γ.neighborSet L) := by
      rw [← hphi, heq]
      exact (Set.inter_self _).symm
    have hxE : E ≠ ptPerp Γ c {x} := by
      intro h
      exact hEβ (by rw [h]; exact ⟨x, hxL, rfl⟩)
    have hstar : IsStarPlane (Γ.induce S) c' (φ (Γ.neighborSet L)) := by
      rw [← hXM]
      exact isStarPlane_inter hΓ hE (Or.inl ⟨x, hx0, rfl⟩) hxE
    have h2le : 2 ≤ (Γ.neighborSet L ∩ E).ncard := by
      have hlt := one_lt_ncard_of_isStarPlane hP' hT' c' hdeg' hreg' hstar
      have hcard : (φ (Γ.neighborSet L)).ncard = (Γ.neighborSet L ∩ E).ncard := by
        rw [← Set.ncard_image_of_injective _ Subtype.val_injective, hvalM]
      omega
    have hLE : Γ.neighborSet L ⊆ E := hE.2.1 L hL h2le
    have hxE' : x ∈ E := hLE (by rwa [SimpleGraph.mem_neighborSet])
    have hyE' : y ∈ E := hLE (by rwa [SimpleGraph.mem_neighborSet])
    have hxS : x ∈ subquadrangleSet Γ c E := mem_subquadrangleSet.mpr (Or.inl hxE')
    have hyS : y ∈ subquadrangleSet Γ c E := mem_subquadrangleSet.mpr (Or.inl hyE')
    have hperpx : φ (ptPerp Γ c {x}) = ptPerp (Γ.induce S) c' {⟨x, hxS⟩} := by
      ext v
      simp only [φ, Set.mem_setOf_eq]
      rw [mem_ptPerp, mem_ptPerp]
      constructor
      · rintro ⟨hv0, hvd⟩
        refine ⟨?_, ?_⟩
        · rw [subquadrangleColoring_apply]
          exact hv0
        · intro u hu
          rw [Set.mem_singleton_iff] at hu
          rw [hu, dist_subquadrangleGraph_of_isFullSubquadrangle hP hTq c hΓ.deg hE v.2 hxS]
          exact hvd x (Set.mem_singleton x)
      · rintro ⟨hv0, hvd⟩
        refine ⟨?_, ?_⟩
        · rwa [subquadrangleColoring_apply] at hv0
        · intro u hu
          rw [Set.mem_singleton_iff] at hu
          rw [hu, ← dist_subquadrangleGraph_of_isFullSubquadrangle hP hTq c hΓ.deg hE v.2 hxS]
          exact hvd ⟨x, hxS⟩ (Set.mem_singleton _)
    have hperpy : φ (ptPerp Γ c {y}) = ptPerp (Γ.induce S) c' {⟨y, hyS⟩} := by
      ext v
      simp only [φ, Set.mem_setOf_eq]
      rw [mem_ptPerp, mem_ptPerp]
      constructor
      · rintro ⟨hv0, hvd⟩
        refine ⟨?_, ?_⟩
        · rw [subquadrangleColoring_apply]
          exact hv0
        · intro u hu
          rw [Set.mem_singleton_iff] at hu
          rw [hu, dist_subquadrangleGraph_of_isFullSubquadrangle hP hTq c hΓ.deg hE v.2 hyS]
          exact hvd y (Set.mem_singleton y)
      · rintro ⟨hv0, hvd⟩
        refine ⟨?_, ?_⟩
        · rwa [subquadrangleColoring_apply] at hv0
        · intro u hu
          rw [Set.mem_singleton_iff] at hu
          rw [hu, ← dist_subquadrangleGraph_of_isFullSubquadrangle hP hTq c hΓ.deg hE v.2 hyS]
          exact hvd ⟨y, hyS⟩ (Set.mem_singleton _)
    have heqp : ptPerp (Γ.induce S) c' {⟨x, hxS⟩} =
        ptPerp (Γ.induce S) c' {⟨y, hyS⟩} := by
      rw [← hperpx, ← hperpy]
      exact heq
    have hxeq : (⟨x, hxS⟩ : subquadrangleSet Γ c E) = ⟨y, hyS⟩ :=
      ptPerp_singleton_injective hP' hT'
        (by rw [subquadrangleColoring_apply]; exact hx0)
        (by rw [subquadrangleColoring_apply]; exact hy0) heqp
    exact hxy' (Subtype.ext_iff.mp hxeq)
  refine ⟨?_, hinj⟩
  have hstarF : ∀ X ∈ φ '' lineBundle Γ c L, IsStarPlane (Γ.induce S) c' X := by
    rintro X ⟨E', ⟨x, hxL, rfl⟩, rfl⟩
    refine isStarPlane_inter hΓ hE
      (Or.inl ⟨x, color_eq_zero_of_adj_of_color_eq_one hL hxL, rfl⟩) ?_
    intro h
    exact hEβ (by rw [h]; exact ⟨x, hxL, rfl⟩)
  have hpair : ∀ X ∈ φ '' lineBundle Γ c L, ∀ Y ∈ φ '' lineBundle Γ c L,
      X ≠ Y → X ∩ Y = φ (Γ.neighborSet L) := by
    rintro X ⟨E', ⟨x, hxL, rfl⟩, rfl⟩ Y ⟨E'', ⟨y, hyL, rfl⟩, rfl⟩ hXY
    have hxy : x ≠ y := by
      intro h
      exact hXY (by rw [h])
    have hne : ptPerp Γ c {x} ≠ ptPerp Γ c {y} := by
      intro h
      exact hxy (ptPerp_singleton_injective hP hTq
        (color_eq_zero_of_adj_of_color_eq_one hL hxL)
        (color_eq_zero_of_adj_of_color_eq_one hL hyL) h)
    have hb : ptPerp Γ c {x} ∩ ptPerp Γ c {y} = Γ.neighborSet L :=
      inter_eq_of_mem_lineBundle hΓ hL ⟨x, hxL, rfl⟩ ⟨y, hyL, rfl⟩ hne
    rw [← hb]
    ext v
    simp [φ]
  have hFcard : (φ '' lineBundle Γ c L).ncard = q ^ 2 + 1 := by
    rw [hinj.ncard_image, ncard_of_isThreeBundle hΓ (Or.inr ⟨L, hL, rfl⟩)]
  have h2card : 1 < (φ '' lineBundle Γ c L).ncard := by
    rw [hFcard]
    have hq2 : 0 < q ^ 2 := pow_pos (by have hq := hΓ.two_le; omega) 2
    omega
  by_cases htwo : 2 ≤ (Γ.neighborSet L ∩ E).ncard
  ·
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (Set.one_lt_ncard (s := Γ.neighborSet L ∩ E)).mp (by omega : 1 < _)
    have haL : Γ.Adj L a := by
      have h := ha.1
      rwa [SimpleGraph.mem_neighborSet] at h
    have hbL : Γ.Adj L b := by
      have h := hb.1
      rwa [SimpleGraph.mem_neighborSet] at h
    have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hL haL
    have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hL hbL
    have hdist : Γ.dist a b = 2 := dist_eq_two_of_adj_of_adj_of_ne hP haL.symm hbL hab
    have haS : a ∈ subquadrangleSet Γ c E := mem_subquadrangleSet.mpr (Or.inl ha.2)
    have hbS : b ∈ subquadrangleSet Γ c E := mem_subquadrangleSet.mpr (Or.inl hb.2)
    have hvalS : Subtype.val '' starLine (Γ.induce S) c' ⟨a, haS⟩ ⟨b, hbS⟩ =
        Γ.neighborSet L ∩ E := by
      have h := starLine_subquadrangle_of_dist_two hΓ hE
        (x := ⟨a, haS⟩) (y := ⟨b, hbS⟩)
        (by rw [subquadrangleColoring_apply]; exact ha0) hdist
      rw [h]
      have hLcn : L = commonNeighbor hP hdist := eq_commonNeighbor hP hdist haL.symm hbL.symm
      rw [← hLcn]
    have hM : φ (Γ.neighborSet L) = starLine (Γ.induce S) c' ⟨a, haS⟩ ⟨b, hbS⟩ :=
      Function.Injective.image_injective Subtype.val_injective (by rw [hvalM, hvalS])
    have hab' : (⟨a, haS⟩ : subquadrangleSet Γ c E) ≠ ⟨b, hbS⟩ :=
      fun h => hab (Subtype.ext_iff.mp h)
    have hline : IsStarLine (Γ.induce S) c' (φ (Γ.neighborSet L)) := by
      rw [hM]
      exact isStarLine_starLine (c := c')
        (by rw [subquadrangleColoring_apply]; exact ha0)
        (by rw [subquadrangleColoring_apply]; exact hb0) hab'
    exact Or.inl ⟨φ (Γ.neighborSet L), hline,
      eq_axisBundle_of_pairwise hP' hT' c' hdeg' hreg' hst' hii'
        hline hstarF hFcard hpair⟩
  ·
    have hle1 : (φ (Γ.neighborSet L)).ncard ≤ 1 := by
      have hcard : (φ (Γ.neighborSet L)).ncard = (Γ.neighborSet L ∩ E).ncard := by
        rw [← Set.ncard_image_of_injective _ Subtype.val_injective, hvalM]
      omega
    obtain ⟨X0, hX0, Y0, hY0, hX0Y0⟩ :=
      (Set.one_lt_ncard (s := φ '' lineBundle Γ c L)).mp h2card
    have hne := inter_nonempty hP' hT' c' hdeg' hreg' hst' hii'
      (hstarF X0 hX0) (hstarF Y0 hY0)
    have hinter : X0 ∩ Y0 = φ (Γ.neighborSet L) := hpair X0 hX0 Y0 hY0 hX0Y0
    have hpos : 0 < (φ (Γ.neighborSet L)).ncard := by
      rw [← hinter]
      exact (Set.ncard_pos (s := X0 ∩ Y0)).mpr hne
    have hone : (φ (Γ.neighborSet L)).ncard = 1 := by omega
    obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hone
    have hpairx : ∀ X ∈ φ '' lineBundle Γ c L, ∀ Y ∈ φ '' lineBundle Γ c L,
        X ≠ Y → X ∩ Y = {x} := by
      intro X hX Y hY hXY
      rw [hpair X hX Y hY hXY, hx]
    obtain ⟨X, hX, hXnon, hFeq⟩ := eq_tangentBundle_of_pairwise hP' hT' c' hdeg' hreg'
      hst' hii' hstarF hFcard hpairx
    have hxX : x ∈ X := by
      obtain ⟨Y, hY, hYX⟩ := Set.exists_ne_of_one_lt_ncard h2card X
      have hXY : X ≠ Y := fun h => hYX h.symm
      have hxint : x ∈ X ∩ Y := by
        rw [hpairx X hX Y hY hXY]
        exact Set.mem_singleton x
      exact hxint.1
    exact Or.inr ⟨X, x, hXnon, hxX, hFeq⟩

theorem isPlaneBundle_image (hΓ : IsThasQuadrangle Γ c q) {β : Set (Set V)}
    (hβ : IsThreeBundle Γ c q β) {E : Set V} (hE : IsFullSubquadrangle c E q) (hEβ : E ∉ β) :
    IsPlaneBundle (Γ.induce (subquadrangleSet Γ c E)) (subquadrangleColoring c E)
        ((fun E' => {v : subquadrangleSet Γ c E | (v : V) ∈ E'}) '' β) ∧
      Set.InjOn (fun E' => {v : subquadrangleSet Γ c E | (v : V) ∈ E'}) β := by
  rcases hβ with ⟨T, hT, rfl⟩ | ⟨L, hL, rfl⟩
  · exact threeBundle_case hΓ hT hE hEβ
  · exact lineBundle_case hΓ hL hE hEβ

end CFSG.Geometry.GeneralizedQuadrangles

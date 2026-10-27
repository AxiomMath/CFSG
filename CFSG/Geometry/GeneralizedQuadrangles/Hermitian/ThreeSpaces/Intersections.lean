module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Bundles2
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Planes
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Planes2
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Pasch
public import Mathlib.Data.Set.Card.Arithmetic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
  {q : ℕ}

theorem color_zero_of_mem_of_isThreespace {E : Set V}
    (hE : IsThreespace Γ c q E) {z : V} (hz : z ∈ E) : c z = 0 := by
  rcases hE with ⟨x, -, rfl⟩ | hF
  · exact hz.1
  · exact hF.1 z hz

private theorem not_subset_neighborSet_of_isPlane (hΓ : IsThasQuadrangle Γ c q) {T : Set V}
    (hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T) {L : V} :
    ¬ T ⊆ Γ.neighborSet L := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hq2 : 2 ≤ q := hΓ.two_le
  have hq : 0 < q := by omega
  have hdist_le_two : ∀ {u v : V}, u ∈ Γ.neighborSet L → v ∈ Γ.neighborSet L →
      Γ.dist u v ≤ 2 := by
    intro u v hu hv
    have h := hP.connected.dist_triangle (u := u) (v := L) (w := v)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hu.symm,
      SimpleGraph.dist_eq_one_iff_adj.mpr hv] at h
    omega
  intro hsub
  rcases hT with ⟨u, v, hu0, huv4, hTeq⟩ | ⟨a, b, z, ha0, hab4, hzT, hTeq⟩
  · have hTcard : T.ncard = q ^ 3 + 1 := by
      rw [hTeq, ncard_trace hP huv4, hΓ.deg u, if_pos hu0]
    have hpos : 0 < T.ncard := by rw [hTcard]; positivity
    obtain ⟨u', hu'T⟩ := (Set.ncard_pos (s := T)).mp hpos
    have h2 : 1 < T.ncard := by
      rw [hTcard]
      have hq3 : 0 < q ^ 3 := pow_pos hq 3
      omega
    obtain ⟨v', hv'T, huv'⟩ := Set.exists_ne_of_one_lt_ncard h2 u'
    have h4 : Γ.dist u' v' = 4 := by
      rw [hTeq] at hu'T hv'T
      exact dist_eq_four_of_mem_trace hP huv4 hu'T hv'T huv'.symm
    have hle : Γ.dist u' v' ≤ 2 :=
      hdist_le_two (hsub hu'T) (hsub hv'T)
    omega
  · have hspancard : (spanSet Γ a b).ncard = q + 1 := hΓ.span a b ha0 hab4
    have h2 : 1 < (spanSet Γ a b).ncard := by rw [hspancard]; omega
    obtain ⟨u, huS⟩ := (Set.ncard_pos (s := spanSet Γ a b)).mp (by rw [hspancard]; omega)
    obtain ⟨v, hvS, huv⟩ := Set.exists_ne_of_one_lt_ncard h2 u
    have hcu : c u = 0 := color_eq_zero_of_mem_span hP hΓ.thick ha0 hab4 huS
    have hcv : c v = 0 := color_eq_zero_of_mem_span hP hΓ.thick ha0 hab4 hvS
    have huT : u ∈ T := by
      rw [hTeq]
      refine ⟨?_, ?_⟩
      · rw [mem_ptPerp]
        exact ⟨hcu, by
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst w
          exact huS z hzT⟩
      · rw [mem_clSet]
        exact ⟨u, huS, by simp⟩
    have hvT : v ∈ T := by
      rw [hTeq]
      refine ⟨?_, ?_⟩
      · rw [mem_ptPerp]
        exact ⟨hcv, by
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst w
          exact hvS z hzT⟩
      · rw [mem_clSet]
        exact ⟨v, hvS, by simp⟩
    have h4 : Γ.dist u v = 4 :=
      dist_eq_four_of_mem_span hP hΓ.thick hab4 huS hvS (Ne.symm huv)
    have hle : Γ.dist u v ≤ 2 :=
      hdist_le_two (hsub huT) (hsub hvT)
    omega

private theorem not_isFullSubquadrangle_ptPerp (hΓ : IsThasQuadrangle Γ c q) {z : V}
    (hz : c z = 0) : ¬ IsFullSubquadrangle c (ptPerp Γ c {z}) q := by
  intro hF
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have h1 : (ptPerp Γ c {z}).ncard = (q ^ 2 + 1) * (q ^ 2 * q + 1) :=
    ncard_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF
  have h2 : (ptPerp Γ c {z}).ncard = q ^ 2 * q ^ 3 + q ^ 2 + 1 :=
    ncard_ptPerp_singleton hP hΓ.thick c hΓ.deg (s := q ^ 2) (t := q ^ 3) hz
  rw [h1] at h2
  have hq : 0 < q := by have h := hΓ.two_le; omega
  have hq3 : 0 < q ^ 3 := pow_pos hq 3
  nlinarith

theorem isStarPlane_inter (hΓ : IsThasQuadrangle Γ c q) {E E' : Set V}
    (hE : IsFullSubquadrangle c E q) (hE' : IsThreespace Γ c q E') (hne : E ≠ E') :
    IsStarPlane (Γ.induce (subquadrangleSet Γ c E)) (subquadrangleColoring c E)
      {v | (v : V) ∈ E'} := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  let ΓE := Γ.induce (subquadrangleSet Γ c E)
  let cE := subquadrangleColoring c E
  let S : Set (Set (subquadrangleSet Γ c E)) := {X | IsStarPlane ΓE cE X}
  let U : Set (subquadrangleSet Γ c E) → Set (Set V) :=
    fun X => {E'' | E'' ∈ threeBundle Γ c q (Subtype.val '' X) ∧ E'' ≠ E}
  have hPE : IsGeneralizedPolygon ΓE 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hΓ.thick c hΓ.deg hE
  have hTE : IsThick ΓE :=
    isThick_subquadrangleGraph hP hΓ.thick c hΓ.deg hE hΓ.two_le
  have hdegE : ∀ v, ΓE.degree v = if cE v = 0 then q + 1 else q ^ 2 + 1 :=
    fun v => degree_subquadrangleGraph hΓ hE v
  have hregE : ∀ x, cE x = 0 → IsRegularVertex ΓE x :=
    fun x hx => isRegularVertex_subquadrangle hΓ hE x hx
  have hst : q ^ 2 ≠ q := by
    intro h
    have hq : 2 ≤ q := hΓ.two_le
    nlinarith
  have hiiE : TalliniCondPrime ΓE cE := talliniCondPrime_subquadrangle hΓ hE
  have hSfin : S.Finite := Set.toFinite S
  have hScard : S.ncard = q ^ 6 + q ^ 4 + q ^ 2 + 1 := by
    have h := ncard_starPlanes hPE hTE cE (s := q ^ 2) (t := q) hdegE hregE hst hiiE
    change S.ncard = (q ^ 2) ^ 3 + (q ^ 2) ^ 2 + q ^ 2 + 1 at h
    rw [h]
    ring
  have hsubE : ∀ {X : Set (subquadrangleSet Γ c E)}, X ∈ S → Subtype.val '' X ⊆ E := by
    intro X hX z hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact mem_P'_of_subquadrangleColoring_eq_zero (hX.1.1.1 v hv)
  have hUcard : ∀ X ∈ S, (U X).ncard = q ^ 2 := by
    intro X hX
    have hTX : IsTracePlane Γ c (Subtype.val '' X) ∨
        IsConePlane Γ c (Subtype.val '' X) :=
      (isStarPlane_subquadrangle_iff hΓ hE).mp hX
    have hβ : IsThreeBundle Γ c q (threeBundle Γ c q (Subtype.val '' X)) :=
      Or.inl ⟨_, hTX, rfl⟩
    have hbcard := ncard_of_isThreeBundle hΓ hβ
    have hE_mem : E ∈ threeBundle Γ c q (Subtype.val '' X) :=
      ⟨Or.inr hE, hsubE hX⟩
    have hset : U X = threeBundle Γ c q (Subtype.val '' X) \ {E} := by
      ext E''
      simp only [U, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    rw [hset, Set.ncard_sdiff_singleton_of_mem hE_mem, hbcard]
    omega
  have hdisj : S.PairwiseDisjoint U := by
    intro X hX Y hY hXY
    change Disjoint (U X) (U Y)
    rw [Set.disjoint_iff_inter_eq_empty]
    ext E''
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hXU hYU
    simp only [U, Set.mem_setOf_eq] at hXU hYU
    have hTX : IsTracePlane Γ c (Subtype.val '' X) ∨
        IsConePlane Γ c (Subtype.val '' X) :=
      (isStarPlane_subquadrangle_iff hΓ hE).mp hX
    have hTY : IsTracePlane Γ c (Subtype.val '' Y) ∨
        IsConePlane Γ c (Subtype.val '' Y) :=
      (isStarPlane_subquadrangle_iff hΓ hE).mp hY
    have hE_mem_X : E ∈ threeBundle Γ c q (Subtype.val '' X) :=
      ⟨Or.inr hE, hsubE hX⟩
    have hE_mem_Y : E ∈ threeBundle Γ c q (Subtype.val '' Y) :=
      ⟨Or.inr hE, hsubE hY⟩
    have h1 : E'' ∩ E = Subtype.val '' X :=
      inter_eq_of_mem_threeBundle hΓ hTX hXU.1 hE_mem_X hXU.2
    have h2 : E'' ∩ E = Subtype.val '' Y :=
      inter_eq_of_mem_threeBundle hΓ hTY hYU.1 hE_mem_Y hYU.2
    have himg : Subtype.val '' X = Subtype.val '' Y := h1.symm.trans h2
    exact hXY ((Set.image_eq_image Subtype.val_injective).mp himg)
  have hUnionCard : (⋃ X ∈ S, U X).ncard = S.ncard * q ^ 2 := by
    calc
      (⋃ X ∈ S, U X).ncard = ∑ᶠ X ∈ S, (U X).ncard :=
        Set.Finite.ncard_biUnion hSfin (fun X _ => Set.toFinite (U X)) hdisj
      _ = ∑ X ∈ hSfin.toFinset, (U X).ncard :=
        finsum_mem_eq_finite_toFinset_sum (fun X => (U X).ncard) hSfin
      _ = hSfin.toFinset.card * q ^ 2 :=
        Finset.sum_const_nat (fun X hX => hUcard X (hSfin.mem_toFinset.mp hX))
      _ = S.ncard * q ^ 2 := by
        rw [Set.ncard_eq_toFinset_card S hSfin]
  let C : Set (Set V) := {E'' | IsThreespace Γ c q E'' ∧ E'' ≠ E}
  have hUnionSub : (⋃ X ∈ S, U X) ⊆ C := by
    rintro E'' hE''
    rw [Set.mem_iUnion] at hE''
    obtain ⟨X, hE''⟩ := hE''
    rw [Set.mem_iUnion] at hE''
    obtain ⟨hXS, hXU⟩ := hE''
    simp only [U, Set.mem_setOf_eq] at hXU
    exact ⟨hXU.1.1, hXU.2⟩
  have hCcard : C.ncard = q ^ 8 + q ^ 6 + q ^ 4 + q ^ 2 := by
    have hall := ncard_threespaces hΓ
    have hE_all : E ∈ {E'' | IsThreespace Γ c q E''} := Or.inr hE
    have hCeq : C = {E'' | IsThreespace Γ c q E''} \ {E} := by
      ext E''
      simp only [C, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    rw [hCeq, Set.ncard_sdiff_singleton_of_mem hE_all, hall]
    omega
  have hUnionCard' : (⋃ X ∈ S, U X).ncard = q ^ 8 + q ^ 6 + q ^ 4 + q ^ 2 := by
    rw [hUnionCard, hScard]
    ring
  have hUnionEq : (⋃ X ∈ S, U X) = C := by
    refine Set.eq_of_subset_of_ncard_le hUnionSub ?_
    rw [hCcard, hUnionCard']
  have hE'C : E' ∈ C := ⟨hE', Ne.symm hne⟩
  have hE'union : E' ∈ ⋃ X ∈ S, U X := by
    rw [hUnionEq]
    exact hE'C
  rw [Set.mem_iUnion] at hE'union
  obtain ⟨X, hE'union⟩ := hE'union
  rw [Set.mem_iUnion] at hE'union
  obtain ⟨hXS, hXU⟩ := hE'union
  simp only [U, Set.mem_setOf_eq] at hXU
  have hTX : IsTracePlane Γ c (Subtype.val '' X) ∨
      IsConePlane Γ c (Subtype.val '' X) :=
    (isStarPlane_subquadrangle_iff hΓ hE).mp hXS
  have hE_mem_X : E ∈ threeBundle Γ c q (Subtype.val '' X) :=
    ⟨Or.inr hE, hsubE hXS⟩
  have hinter : E' ∩ E = Subtype.val '' X :=
    inter_eq_of_mem_threeBundle hΓ hTX hXU.1 hE_mem_X hXU.2
  let Y : Set (subquadrangleSet Γ c E) := {v | (v : V) ∈ E'}
  have hYimg : Subtype.val '' Y = E' ∩ E := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : (v : V) ∈ E' := hv
      have hcz : c (v : V) = 0 := color_zero_of_mem_of_isThreespace hE' hv'
      refine ⟨hv', ?_⟩
      exact mem_P'_of_subquadrangleColoring_eq_zero (by
        rw [subquadrangleColoring_apply]
        exact hcz)
    · rintro ⟨hzE', hzE⟩
      exact ⟨⟨z, mem_subquadrangleSet.mpr (Or.inl hzE)⟩, hzE', rfl⟩
  have hYX : Y = X := by
    have himg : Subtype.val '' Y = Subtype.val '' X := hYimg.trans hinter
    exact (Set.image_eq_image Subtype.val_injective).mp himg
  change IsStarPlane ΓE cE Y
  rw [hYX]
  exact hXS

private theorem existsUnique_isThreeBundle_of_isFullSubquadrangle
    (hΓ : IsThasQuadrangle Γ c q) {E E' : Set V} (hE : IsFullSubquadrangle c E q)
    (hE' : IsThreespace Γ c q E') (hne : E ≠ E') :
    ∃! β, IsThreeBundle Γ c q β ∧ E ∈ β ∧ E' ∈ β := by
  classical
  let X : Set (subquadrangleSet Γ c E) := {v | (v : V) ∈ E'}
  have hX : IsStarPlane (Γ.induce (subquadrangleSet Γ c E))
      (subquadrangleColoring c E) X := isStarPlane_inter hΓ hE hE' hne
  let T : Set V := Subtype.val '' X
  have hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T :=
    (isStarPlane_subquadrangle_iff hΓ hE).mp hX
  have hTE : T ⊆ E := by
    rintro z ⟨v, hv, rfl⟩
    exact mem_P'_of_subquadrangleColoring_eq_zero (hX.1.1.1 v hv)
  have hEβ : E ∈ threeBundle Γ c q T := ⟨Or.inr hE, hTE⟩
  have hE'β : E' ∈ threeBundle Γ c q T := by
    refine ⟨hE', ?_⟩
    rintro z ⟨v, hv, rfl⟩
    exact hv
  have hβ : IsThreeBundle Γ c q (threeBundle Γ c q T) := Or.inl ⟨T, hT, rfl⟩
  have hinter : E ∩ E' = T := inter_eq_of_mem_threeBundle hΓ hT hEβ hE'β hne
  refine ⟨threeBundle Γ c q T, ⟨hβ, hEβ, hE'β⟩, ?_⟩
  rintro γ ⟨hγ, hEγ, hE'γ⟩
  rcases hγ with ⟨T₀, hT₀, rfl⟩ | ⟨L, hL, rfl⟩
  · have h : E ∩ E' = T₀ := inter_eq_of_mem_threeBundle hΓ hT₀ hEγ hE'γ hne
    have hT₀eq : T₀ = T := h.symm.trans hinter
    rw [hT₀eq]
  · obtain ⟨z, hLz, hEz⟩ := hEγ
    have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLz
    have hfull : IsFullSubquadrangle c (ptPerp Γ c {z}) q := hEz ▸ hE
    exact (not_isFullSubquadrangle_ptPerp hΓ hz0 hfull).elim

theorem existsUnique_isThreeBundle (hΓ : IsThasQuadrangle Γ c q) {E E' : Set V}
    (hE : IsThreespace Γ c q E) (hE' : IsThreespace Γ c q E') (hne : E ≠ E') :
    ∃! β, IsThreeBundle Γ c q β ∧ E ∈ β ∧ E' ∈ β := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  rcases hE with ⟨x, hx0, rfl⟩ | hEfull
  · rcases hE' with ⟨y, hy0, rfl⟩ | hE'full
    · have hxyne : x ≠ y := by
        intro hxy
        exact hne (by rw [hxy])
      rcases dist_eq_two_or_four_of_color_zero hP hx0 hy0 hxyne with hxy2 | hxy4
      · let L : V := commonNeighbor hP hxy2
        have hxL : Γ.Adj L x := (commonNeighbor_adj_left hP hxy2).symm
        have hyL : Γ.Adj L y := (commonNeighbor_adj_right hP hxy2).symm
        have hL1 : c L = 1 :=
          color_eq_one_of_adj_of_color_eq_zero hx0 (commonNeighbor_adj_left hP hxy2)
        have hEβ : ptPerp Γ c {x} ∈ lineBundle Γ c L := ⟨x, hxL, rfl⟩
        have hE'β : ptPerp Γ c {y} ∈ lineBundle Γ c L := ⟨y, hyL, rfl⟩
        refine ⟨lineBundle Γ c L, ⟨Or.inr ⟨L, hL1, rfl⟩, hEβ, hE'β⟩, ?_⟩
        rintro γ ⟨hγ, hEγ, hE'γ⟩
        rcases hγ with ⟨T, hT, rfl⟩ | ⟨L', hL'1, rfl⟩
        · have h1 : ptPerp Γ c {x} ∩ ptPerp Γ c {y} = T :=
            inter_eq_of_mem_threeBundle hΓ hT hEγ hE'γ hne
          have h2 : ptPerp Γ c {x} ∩ ptPerp Γ c {y} = Γ.neighborSet L :=
            inter_eq_of_mem_lineBundle hΓ hL1 hEβ hE'β hne
          have hTNeigh : T = Γ.neighborSet L := h1.symm.trans h2
          have hsubN : T ⊆ Γ.neighborSet L := by rw [hTNeigh]
          exact (not_subset_neighborSet_of_isPlane hΓ hT hsubN).elim
        · have h2 : ptPerp Γ c {x} ∩ ptPerp Γ c {y} = Γ.neighborSet L' :=
            inter_eq_of_mem_lineBundle hΓ hL'1 hEγ hE'γ hne
          have h2' : ptPerp Γ c {x} ∩ ptPerp Γ c {y} = Γ.neighborSet L :=
            inter_eq_of_mem_lineBundle hΓ hL1 hEβ hE'β hne
          have hN : Γ.neighborSet L' = Γ.neighborSet L := h2.symm.trans h2'
          have hxN' : x ∈ Γ.neighborSet L' := by rw [hN]; exact hxL
          have hyN' : y ∈ Γ.neighborSet L' := by rw [hN]; exact hyL
          have hLL' : L' = L :=
            (existsUnique_commonNeighbor hP hxy2).unique
              ⟨hxN'.symm, hyN'.symm⟩
              ⟨commonNeighbor_adj_left hP hxy2, commonNeighbor_adj_right hP hxy2⟩
          rw [hLL']
      · let T : Set V := traceSet Γ x y
        have hT : IsTracePlane Γ c T := ⟨x, y, hx0, hxy4, rfl⟩
        have hxT : ptPerp Γ c {x} ∈ threeBundle Γ c q T := by
          refine ⟨Or.inl ⟨x, hx0, rfl⟩, ?_⟩
          intro z hz
          rw [mem_ptPerp]
          exact ⟨color_eq_zero_of_dist_eq_two hP hx0 hz.1, by
            intro w hw
            rw [Set.mem_singleton_iff] at hw
            subst w
            rw [SimpleGraph.dist_comm]
            exact le_of_eq hz.1⟩
        have hyT : ptPerp Γ c {y} ∈ threeBundle Γ c q T := by
          refine ⟨Or.inl ⟨y, hy0, rfl⟩, ?_⟩
          intro z hz
          rw [mem_ptPerp]
          exact ⟨color_eq_zero_of_dist_eq_two hP hy0 hz.2, by
            intro w hw
            rw [Set.mem_singleton_iff] at hw
            subst w
            rw [SimpleGraph.dist_comm]
            exact le_of_eq hz.2⟩
        have hinterTrace : ptPerp Γ c {x} ∩ ptPerp Γ c {y} = T := by
          ext z
          constructor
          · rintro ⟨hxZ, hyZ⟩
            rw [mem_ptPerp] at hxZ hyZ
            have hz0 : c z = 0 := hxZ.1
            have hzxne : z ≠ x := by
              intro h
              subst z
              have hle := hyZ.2 y (by simp)
              omega
            have hzyne : z ≠ y := by
              intro h
              subst z
              have hle := hxZ.2 x (by simp)
              have h4 : Γ.dist y x = 4 := by rwa [SimpleGraph.dist_comm]
              omega
            have hzx : Γ.dist z x = 2 :=
              dist_eq_two_of_le_two_of_ne hP hz0 hx0 hzxne (hxZ.2 x (by simp))
            have hzy : Γ.dist z y = 2 :=
              dist_eq_two_of_le_two_of_ne hP hz0 hy0 hzyne (hyZ.2 y (by simp))
            exact ⟨by rwa [SimpleGraph.dist_comm], by rwa [SimpleGraph.dist_comm]⟩
          · rintro ⟨hzx, hzy⟩
            constructor
            · rw [mem_ptPerp]
              exact ⟨color_eq_zero_of_dist_eq_two hP hx0 hzx, by
                intro w hw
                rw [Set.mem_singleton_iff] at hw
                subst w
                rw [SimpleGraph.dist_comm]
                exact le_of_eq hzx⟩
            · rw [mem_ptPerp]
              exact ⟨color_eq_zero_of_dist_eq_two hP hy0 hzy, by
                intro w hw
                rw [Set.mem_singleton_iff] at hw
                subst w
                rw [SimpleGraph.dist_comm]
                exact le_of_eq hzy⟩
        refine ⟨threeBundle Γ c q T, ⟨Or.inl ⟨T, Or.inl hT, rfl⟩, hxT, hyT⟩, ?_⟩
        rintro γ ⟨hγ, hEγ, hE'γ⟩
        rcases hγ with ⟨T₀, hT₀, rfl⟩ | ⟨L', hL'1, rfl⟩
        · have h1 : ptPerp Γ c {x} ∩ ptPerp Γ c {y} = T₀ :=
            inter_eq_of_mem_threeBundle hΓ hT₀ hEγ hE'γ hne
          have hT₀eq : T₀ = T := h1.symm.trans hinterTrace
          rw [hT₀eq]
        · have h1 : ptPerp Γ c {x} ∩ ptPerp Γ c {y} = Γ.neighborSet L' :=
            inter_eq_of_mem_lineBundle hΓ hL'1 hEγ hE'γ hne
          have heq : T = Γ.neighborSet L' := hinterTrace.symm.trans h1
          have heqcard : T.ncard = (Γ.neighborSet L').ncard := congrArg Set.ncard heq
          have hTcard : T.ncard = q ^ 3 + 1 := by
            change (traceSet Γ x y).ncard = q ^ 3 + 1
            rw [ncard_trace hP hxy4, hΓ.deg x, if_pos hx0]
          have hNcard : (Γ.neighborSet L').ncard = q ^ 2 + 1 := by
            rw [SimpleGraph.ncard_neighborSet, hΓ.deg L',
              if_neg (by rw [hL'1]; decide)]
          have heq' : q ^ 3 + 1 = q ^ 2 + 1 := by
            rw [← hTcard, ← hNcard]
            exact heqcard
          have hlt : q ^ 2 < q ^ 3 :=
            Nat.pow_lt_pow_right (by have h := hΓ.two_le; omega : 1 < q) (by norm_num : 2 < 3)
          omega
    · have h := existsUnique_isThreeBundle_of_isFullSubquadrangle (E := E')
          (E' := ptPerp Γ c {x}) hΓ hE'full (Or.inl ⟨x, hx0, rfl⟩) (Ne.symm hne)
      exact (existsUnique_congr (fun β => by
        constructor
        · rintro ⟨hβ, hβ1, hβ2⟩
          exact ⟨hβ, hβ2, hβ1⟩
        · rintro ⟨hβ, hβ1, hβ2⟩
          exact ⟨hβ, hβ2, hβ1⟩)).mp h
  · exact existsUnique_isThreeBundle_of_isFullSubquadrangle hΓ hEfull hE' hne

end CFSG.Geometry.GeneralizedQuadrangles

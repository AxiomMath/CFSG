module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.PlanesThrough2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section BundleVocabulary

variable (Γ : SimpleGraph V) (c : Γ.Coloring (Fin 2))

@[expose] def axisBundle (L : Set V) : Set (Set V) := {X | IsStarPlane Γ c X ∧ L ⊆ X}

@[expose] def tangentBundle (X : Set V) (x : V) : Set (Set V) :=
  {Y | IsStarPlane Γ c Y ∧ (Y = X ∨ X ∩ Y = {x})}

@[expose] def IsPlaneBundle (β : Set (Set V)) : Prop :=
  (∃ L, IsStarLine Γ c L ∧ β = axisBundle Γ c L) ∨
    ∃ X x, IsNonabsPlane Γ c X ∧ x ∈ X ∧ β = tangentBundle Γ c X x

end BundleVocabulary

section BundleAux

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ptPerp_singleton_injective (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {u v : V} (hu : c u = 0) (hv : c v = 0)
    (h : ptPerp Γ c {u} = ptPerp Γ c {v}) : u = v := by
  classical
  by_contra huv
  have hv_perp : v ∈ ptPerp Γ c {u} := by
    rw [h]
    rw [mem_ptPerp]
    exact ⟨hv, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; simp⟩
  have hle : Γ.dist u v ≤ 2 := by
    have := (mem_ptPerp.mp hv_perp).2 u (by simp)
    simpa [SimpleGraph.dist_comm] using this
  have h2 : Γ.dist u v = 2 := dist_eq_two_of_le_two_of_ne hP hu hv huv hle
  have huK : Γ.Adj u (commonNeighbor hP h2) := commonNeighbor_adj_left hP h2
  have hposN : 0 < ((Γ.neighborFinset u).erase (commonNeighbor hP h2)).card := by
    rw [Finset.card_erase_of_mem (by simpa [mem_neighborFinset] using huK),
      card_neighborFinset_eq_degree]
    have := hT u
    omega
  obtain ⟨N, hN⟩ := Finset.card_pos.mp hposN
  rw [Finset.mem_erase, mem_neighborFinset] at hN
  have hNK : N ≠ commonNeighbor hP h2 := hN.1
  have huN : Γ.Adj u N := hN.2
  have hposw : 0 < ((Γ.neighborFinset N).erase u).card := by
    rw [Finset.card_erase_of_mem (by simpa [mem_neighborFinset] using huN.symm),
      card_neighborFinset_eq_degree]
    have := hT N
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hposw
  rw [Finset.mem_erase, mem_neighborFinset] at hw
  have hwu : w ≠ u := hw.1
  have hNw : Γ.Adj N w := hw.2
  have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hu huN
  have hw0 : c w = 0 := color_eq_zero_of_adj_of_color_eq_one hN1 hNw
  have hwperp : w ∈ ptPerp Γ c {u} := neighborSet_subset_ptPerp hP hN1 huN (by simpa using hNw)
  have hwperp' : w ∈ ptPerp Γ c {v} := by rw [← h]; exact hwperp
  have hle' : Γ.dist w v ≤ 2 := (mem_ptPerp.mp hwperp').2 v (by simp)
  have hwv : w ≠ v := by
    intro hwv
    apply hNK
    exact eq_commonNeighbor hP h2 huN (by rw [← hwv]; exact hNw.symm)
  have h2' : Γ.dist w v = 2 := dist_eq_two_of_le_two_of_ne hP hw0 hv hwv hle'
  have hvN : ¬ Γ.Adj v N := by
    intro hvN
    exact hNK (eq_commonNeighbor hP h2 huN hvN)
  have heq : u = w :=
    eq_of_adj_of_dist_two_of_not_adj (c := c) hP hvN huN.symm hNw
      (by rw [SimpleGraph.dist_comm]; exact h2) (by rw [SimpleGraph.dist_comm]; exact h2')
  exact hwu heq.symm

theorem inter_ptPerp_eq_singleton_of_isNonabsPlane (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {c : Γ.Coloring (Fin 2)} {X : Set V} (hX : IsNonabsPlane Γ c X)
    {x : V} (hx : x ∈ X) : X ∩ ptPerp Γ c {x} = {x} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨hzX, hzperp⟩
    have hx0 : c x = 0 := hX.1.1.1.1 x hx
    have hle : Γ.dist z x ≤ 2 := (mem_ptPerp.mp hzperp).2 x (by simp)
    by_contra hzx
    have h4 : Γ.dist z x = 4 := dist_eq_four_of_mem_of_isOvoid hP hT hX.2 hzX hx hzx
    omega
  · rintro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    refine ⟨hx, ?_⟩
    rw [mem_ptPerp]
    exact ⟨hX.1.1.1.1 x hx, by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      simp⟩

theorem not_subset_ptPerp_singleton_of_isHypLine (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {c : Γ.Coloring (Fin 2)} {x : V} (hx : c x = 0) {ℓ : Set V}
    (hℓ : IsHypLine Γ c ℓ) (hxℓ : x ∈ ℓ) : ¬ ℓ ⊆ ptPerp Γ c {x} := by
  obtain ⟨y, hy4, hℓeq⟩ := exists_starLine_eq_of_mem_of_isHypLine hP hT hℓ hxℓ hx
  have hy0 : c y = 0 := by
    rw [← color_eq_of_dist_four hP hy4]
    exact hx
  have hyℓ : y ∈ ℓ := by
    rw [hℓeq]
    exact mem_starLine_right hy0
  intro hsub
  have hyperp : y ∈ ptPerp Γ c {x} := hsub hyℓ
  have hle : Γ.dist y x ≤ 2 := (mem_ptPerp.mp hyperp).2 x (by simp)
  rw [SimpleGraph.dist_comm] at hle
  omega

theorem not_inter_eq_singleton_of_isAbsPlane (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {X Y : Set V}
    (hX : IsAbsPlane Γ c X) (hY : IsAbsPlane Γ c Y) (hXY : X ≠ Y) {x : V}
    (hx : X ∩ Y = {x}) : False := by
  classical
  obtain ⟨u, hu, rfl⟩ := hX
  obtain ⟨v, hv, rfl⟩ := hY
  have huv : u ≠ v := by
    intro h
    exact hXY (by rw [h])
  rcases dist_eq_two_or_four_of_color_zero hP hu hv huv with h2 | h4
  · have huY : u ∈ ptPerp Γ c {v} := by
      rw [mem_ptPerp]
      refine ⟨hu, ?_⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      simpa [SimpleGraph.dist_comm] using le_of_eq h2
    have huX : u ∈ ptPerp Γ c {u} := by
      rw [mem_ptPerp]
      exact ⟨hu, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; simp⟩
    have hvX : v ∈ ptPerp Γ c {u} := by
      rw [mem_ptPerp]
      refine ⟨hv, ?_⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      rw [SimpleGraph.dist_comm]
      exact le_of_eq h2
    have hvY : v ∈ ptPerp Γ c {v} := by
      rw [mem_ptPerp]
      exact ⟨hv, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; simp⟩
    have hux : u = x := by
      have hmem : u ∈ ({x} : Set V) := by rw [← hx]; exact ⟨huX, huY⟩
      simpa using hmem
    have hvx : v = x := by
      have hmem : v ∈ ({x} : Set V) := by rw [← hx]; exact ⟨hvX, hvY⟩
      simpa using hmem
    exact huv (hux.trans hvx.symm)
  · have hsub : traceSet Γ u v ⊆ ({x} : Set V) := by
      intro w hw
      have hw0 : c w = 0 := color_eq_zero_of_dist_eq_two hP hu hw.1
      have hmem : w ∈ ptPerp Γ c {u} ∩ ptPerp Γ c {v} := by
        constructor
        · rw [mem_ptPerp]
          refine ⟨hw0, ?_⟩
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          rw [SimpleGraph.dist_comm]
          exact le_of_eq hw.1
        · rw [mem_ptPerp]
          refine ⟨hw0, ?_⟩
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          rw [SimpleGraph.dist_comm]
          exact le_of_eq hw.2
      exact hx ▸ hmem
    have hcard : (traceSet Γ u v).ncard = t + 1 := by
      rw [ncard_trace hP h4, degree_eq_t_add_one_of_color_zero hdeg hu]
    have hle : (traceSet Γ u v).ncard ≤ 1 := by
      have h := Set.ncard_le_ncard hsub
      simpa using h
    have ht : 2 ≤ t := two_le_t hP hT c hdeg
    omega

end BundleAux

section BundleIntersections

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem inter_eq_of_mem_axisBundle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {L : Set V} (hL : IsStarLine Γ c L)
    {X Y : Set V} (hX : X ∈ axisBundle Γ c L) (hY : Y ∈ axisBundle Γ c L) (hXY : X ≠ Y) :
    X ∩ Y = L := by
  classical
  rw [axisBundle] at hX hY
  obtain ⟨hXplane, hLX⟩ := hX
  obtain ⟨hYplane, hLY⟩ := hY
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hL
  have haL : a ∈ starLine Γ c a b := mem_starLine_left ha
  have hbL : b ∈ starLine Γ c a b := mem_starLine_right hb
  have haI : a ∈ X ∩ Y := ⟨hLX haL, hLY haL⟩
  have hbI : b ∈ X ∩ Y := ⟨hLX hbL, hLY hbL⟩
  rcases inter_cases hP hT c hdeg hreg hXplane hYplane hXY with hemp | ⟨z, hz⟩ | hline
  · rw [hemp] at haI
    exact absurd haI (by simp)
  · rw [hz] at haI hbI
    have haz : a = z := by simpa using haI
    have hbz : b = z := by simpa using hbI
    exact absurd (haz.trans hbz.symm) hab
  · exact starLine_eq_of_isStarLine_of_mem hP hT hline haI hbI hab

theorem inter_eq_of_mem_tangentBundle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c)
    {X : Set V} {x : V} (hX : IsNonabsPlane Γ c X) (hx : x ∈ X) {Y Z : Set V}
    (hY : Y ∈ tangentBundle Γ c X x) (hZ : Z ∈ tangentBundle Γ c X x) (hYZ : Y ≠ Z) :
    Y ∩ Z = {x} := by
  classical
  rw [tangentBundle] at hY hZ
  obtain ⟨hYplane, hYdisj⟩ := hY
  obtain ⟨hZplane, hZdisj⟩ := hZ
  rcases hYdisj with hYX | hYinter
  · subst hYX
    rcases hZdisj with hZX | hZinter
    · exact absurd hZX.symm hYZ
    · exact hZinter
  · rcases hZdisj with hZX | hZinter
    · subst hZX
      rw [Set.inter_comm]
      exact hYinter
    · have hxY : x ∈ Y := by
        have h : x ∈ X ∩ Y := by rw [hYinter]; simp
        exact h.2
      have hxZ : x ∈ Z := by
        have h : x ∈ X ∩ Z := by rw [hZinter]; simp
        exact h.2
      by_contra hne
      have hxYZ : x ∈ Y ∩ Z := ⟨hxY, hxZ⟩
      rcases inter_cases hP hT c hdeg hreg hYplane hZplane hYZ with hemp | ⟨w, hw⟩ | hline
      · rw [hemp] at hxYZ
        exact absurd hxYZ (by simp)
      · have hwx : w = x := by
          rw [hw] at hxYZ
          simpa [eq_comm] using hxYZ
        exact hne (by rw [hw, hwx])
      · have hsing : ¬ IsStarLine Γ c ({x} : Set V) := by
          rintro ⟨a, b, ha, hb, hab, hEq⟩
          have ha' : a ∈ ({x} : Set V) := by rw [hEq]; exact mem_starLine_left ha
          have hb' : b ∈ ({x} : Set V) := by rw [hEq]; exact mem_starLine_right hb
          exact hab (by simpa using ha'.trans hb'.symm)
        have hYne : Y ≠ ptPerp Γ c {x} := by
          intro hYperp
          have hZne : Z ≠ ptPerp Γ c {x} := fun h => hYZ (hYperp.trans h.symm)
          have hZnon : IsNonabsPlane Γ c Z :=
            isNonabsPlane_of_inter_eq_singleton hP hT c hdeg hreg hX hZplane hZinter hZne
          have hYZeq : Y ∩ Z = {x} := by
            rw [hYperp, Set.inter_comm]
            exact inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hZnon hxZ
          exact hsing (hYZeq ▸ hline)
        have hZne : Z ≠ ptPerp Γ c {x} := by
          intro hZperp
          have hYne' : Y ≠ ptPerp Γ c {x} := fun h => hYZ (h.trans hZperp.symm)
          have hYnon : IsNonabsPlane Γ c Y :=
            isNonabsPlane_of_inter_eq_singleton hP hT c hdeg hreg hX hYplane hYinter hYne'
          have hYZeq : Y ∩ Z = {x} := by
            rw [hZperp]
            exact inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hYnon hxY
          exact hsing (hYZeq ▸ hline)
        have hYnon : IsNonabsPlane Γ c Y :=
          isNonabsPlane_of_inter_eq_singleton hP hT c hdeg hreg hX hYplane hYinter hYne
        have hZnon : IsNonabsPlane Γ c Z :=
          isNonabsPlane_of_inter_eq_singleton hP hT c hdeg hreg hX hZplane hZinter hZne
        obtain ⟨a, b, ha, hb, hab, hℓeq⟩ := hline
        have haI : a ∈ Y ∩ Z := by rw [hℓeq]; exact mem_starLine_left ha
        have hbI : b ∈ Y ∩ Z := by rw [hℓeq]; exact mem_starLine_right hb
        have h4 : Γ.dist a b = 4 :=
          dist_eq_four_of_mem_of_isOvoid hP hT hYnon.2 haI.1 hbI.1 hab
        have hℓhyp : IsHypLine Γ c (Y ∩ Z) := ⟨a, b, ha, h4, hℓeq⟩
        have hℓnotX : ¬ (Y ∩ Z) ⊆ X := by
          intro hsub
          have hsubx : Y ∩ Z ⊆ ({x} : Set V) := by
            intro z hz
            have hzX : z ∈ X := hsub hz
            have hzY : z ∈ Y := hz.1
            have hmem : z ∈ X ∩ Y := ⟨hzX, hzY⟩
            rwa [hYinter] at hmem
          exact hab (by
            have ha' : a ∈ ({x} : Set V) := hsubx haI
            have hb' : b ∈ ({x} : Set V) := hsubx hbI
            simpa using ha'.trans hb'.symm)
        obtain ⟨W, -, huniq⟩ :=
          existsUnique_tangent hP hT c hdeg hreg hii hX hx hℓhyp hxYZ hℓnotX
        have hYeq : Y = W := huniq Y ⟨hYplane, Set.inter_subset_left, hYinter⟩
        have hZeq : Z = W := huniq Z ⟨hZplane, Set.inter_subset_right, hZinter⟩
        exact hYZ (hYeq.trans hZeq.symm)

end BundleIntersections

section TangentBundle

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem tangentBundle_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c)
    {X Y : Set V} {x : V} (hX : IsNonabsPlane Γ c X) (hx : x ∈ X)
    (hY : Y ∈ tangentBundle Γ c X x) (hY' : IsNonabsPlane Γ c Y) :
    tangentBundle Γ c Y x = tangentBundle Γ c X x := by
  classical
  rw [tangentBundle] at hY
  obtain ⟨hYplane, hYX | hYinter⟩ := hY
  · subst hYX
    rfl
  · have hxY : x ∈ Y := by
      have h : x ∈ X ∩ Y := by rw [hYinter]; simp
      exact h.2
    have hYX' : Y ∩ X = {x} := by rw [Set.inter_comm]; exact hYinter
    have hXY : X ∈ tangentBundle Γ c Y x := by
      rw [tangentBundle]
      exact ⟨hX.1, Or.inr hYX'⟩
    have hYXmem : Y ∈ tangentBundle Γ c X x := by
      rw [tangentBundle]
      exact ⟨hYplane, Or.inr hYinter⟩
    refine Set.Subset.antisymm ?_ ?_
    · rintro Z hZ
      rw [tangentBundle] at hZ
      obtain ⟨hZplane, hZYeq | hZYint⟩ := hZ
      · rw [hZYeq]
        exact ⟨hYplane, Or.inr hYinter⟩
      · by_cases hZX : Z = X
        · rw [hZX]
          exact ⟨hX.1, Or.inl rfl⟩
        · have hXZ : X ∩ Z = {x} :=
            inter_eq_of_mem_tangentBundle hP hT c hdeg hreg hii hY' hxY hXY
              (by rw [tangentBundle]; exact ⟨hZplane, Or.inr hZYint⟩)
              (by intro h; exact hZX h.symm)
          exact ⟨hZplane, Or.inr hXZ⟩
    · rintro Z hZ
      rw [tangentBundle] at hZ
      obtain ⟨hZplane, hZXeq | hZXint⟩ := hZ
      · rw [hZXeq]
        exact ⟨hX.1, Or.inr hYX'⟩
      · by_cases hZY : Z = Y
        · rw [hZY]
          exact ⟨hYplane, Or.inl rfl⟩
        · have hYZ : Y ∩ Z = {x} :=
            inter_eq_of_mem_tangentBundle hP hT c hdeg hreg hii hX hx hYXmem
              (by rw [tangentBundle]; exact ⟨hZplane, Or.inr hZXint⟩)
              (by intro h; exact hZY h.symm)
          exact ⟨hZplane, Or.inr hYZ⟩

end TangentBundle

section BundleCardinality

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem ncard_axisBundle_of_dist_two (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {a b : V} (ha : c a = 0) (hb : c b = 0)
    (hab : a ≠ b) (h2 : Γ.dist a b = 2) :
    (axisBundle Γ c (starLine Γ c a b)).ncard = s + 1 := by
  classical
  have hK1 : c (commonNeighbor hP h2) = 1 :=
    color_eq_one_of_adj_of_color_eq_zero ha (commonNeighbor_adj_left hP h2)
  have hLeq : starLine Γ c a b = Γ.neighborSet (commonNeighbor hP h2) :=
    starLine_eq_neighborSet hP hT c ha h2
  have hlin : IsStarLine Γ c (starLine Γ c a b) := isStarLine_starLine ha hb hab
  have haL : a ∈ starLine Γ c a b := mem_starLine_left ha
  have hset : axisBundle Γ c (starLine Γ c a b) =
      Set.range (fun u : ↥(starLine Γ c a b) => ptPerp Γ c {u.1}) := by
    ext X
    constructor
    · rintro ⟨hXplane, hLX⟩
      rw [hLeq] at hLX
      have hex : ∃ w, w ∈ X ∧ w ∉ Γ.neighborSet (commonNeighbor hP h2) := by
        by_contra hall
        push Not at hall
        obtain ⟨x0, hx0, y0, hy0, z0, hz0, hnc⟩ := hXplane.2
        exact hnc ⟨Γ.neighborSet (commonNeighbor hP h2), by rw [← hLeq]; exact hlin,
          hall x0 hx0, hall y0 hy0, hall z0 hz0⟩
      obtain ⟨w, hwX, hwL⟩ := hex
      have hwK : ¬ Γ.Adj (commonNeighbor hP h2) w :=
        fun h => hwL (by simpa [mem_neighborSet] using h)
      have hw0 : c w = 0 := hXplane.1.1.1 w hwX
      obtain ⟨u, ⟨huK, hwu⟩, -⟩ :=
        existsUnique_proj_of_not_adj hP hw0 hK1 (fun h => hwK h.symm)
      have hXeq : X = ptPerp Γ c {u} :=
        eq_ptPerp_of_isProperVariety hP hT c hdeg hreg hXplane.1 hK1 hLX hwX hwK huK hwu
      exact ⟨⟨u, by rw [hLeq]; exact huK⟩, hXeq.symm⟩
    · rintro ⟨u, rfl⟩
      have hu0 : c (u : V) = 0 := u.2.1
      have huK : (u : V) ∈ Γ.neighborSet (commonNeighbor hP h2) := by
        rw [← hLeq]
        exact u.2
      have huK' : Γ.Adj (u : V) (commonNeighbor hP h2) := by
        have h := huK
        simp only [mem_neighborSet] at h
        exact h.symm
      change IsStarPlane Γ c (ptPerp Γ c {(u : V)}) ∧
        starLine Γ c a b ⊆ ptPerp Γ c {(u : V)}
      refine ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hu0, ?_⟩
      intro z hz
      have hzK : z ∈ Γ.neighborSet (commonNeighbor hP h2) := by
        rw [hLeq] at hz
        exact hz
      exact neighborSet_subset_ptPerp hP hK1 huK' hzK
  rw [hset]
  have hinj : Function.Injective (fun u : ↥(starLine Γ c a b) => ptPerp Γ c {u.1}) := by
    intro u v huv
    apply Subtype.ext
    exact ptPerp_singleton_injective hP hT (color_eq_zero_of_mem_starLine u.2)
      (color_eq_zero_of_mem_starLine v.2) huv
  rw [Set.ncard_range_of_injective hinj, Nat.card_coe_set_eq, hLeq, SimpleGraph.ncard_neighborSet,
    hdeg (commonNeighbor hP h2), if_neg (by rw [hK1]; decide)]

private theorem ncard_tangentBundle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c)
    {X : Set V} {x : V} (hX : IsNonabsPlane Γ c X) (hx : x ∈ X) :
    (tangentBundle Γ c X x).ncard = s + 1 := by
  classical
  have hx0 : c x = 0 := hX.1.1.1.1 x hx
  have hXne : X ≠ ptPerp Γ c {x} := ne_ptPerp_of_isNonabsPlane hP hT c hdeg hX hx
  have hXint : X ∩ ptPerp Γ c {x} = {x} :=
    inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hX hx
  let Lall : Finset (Set V) :=
    Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ¬ ℓ ⊆ X)
  let Bfs : Finset (Set V) :=
    Finset.univ.filter (fun Y => IsNonabsPlane Γ c Y ∧ x ∈ Y ∧ X ∩ Y = {x})
  let Lfs : Set V → Finset (Set V) :=
    fun Y => Finset.univ.filter (fun ℓ => IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ Y)
  have hLallcard : Lall.card = s ^ 2 - s := by
    have hset : (Lall : Set (Set V)) =
        {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ} \ {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ X} := by
      ext ℓ
      simp only [Lall, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
        Set.mem_setOf_eq]
      tauto
    have hsub : {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ X} ⊆
        {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ} := fun ℓ h => ⟨h.1, h.2.1⟩
    have h1 : {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ}.ncard = s ^ 2 :=
      ncard_hypLines_through hP hT c hdeg hreg hx0
    have h2 : {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ X}.ncard = s :=
      ncard_hypLines_through_subset hP hT c hdeg hreg hX.1 hx hXne
    rw [← Set.ncard_coe_finset, hset, Set.ncard_sdiff hsub, h1, h2]
  have hfiber : ∀ Y ∈ Bfs, (Lfs Y).card = s := by
    intro Y hY
    rw [Finset.mem_filter] at hY
    obtain ⟨-, hYnon, hxY, -⟩ := hY
    have hcard : {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ Y}.ncard = s :=
      ncard_hypLines_through_subset hP hT c hdeg hreg hYnon.1 hxY
        (ne_ptPerp_of_isNonabsPlane hP hT c hdeg hYnon hxY)
    have hcoe : ((Lfs Y : Finset (Set V)) : Set (Set V)) =
        {ℓ | IsHypLine Γ c ℓ ∧ x ∈ ℓ ∧ ℓ ⊆ Y} := by
      ext ℓ
      simp [Lfs]
    rw [← Set.ncard_coe_finset, hcoe, hcard]
  have hdisj : (↑Bfs : Set (Set V)).PairwiseDisjoint Lfs := by
    intro Y1 hY1 Y2 hY2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ℓ hℓ1 hℓ2
    rw [Finset.mem_coe, Finset.mem_filter] at hY1 hY2
    dsimp only [Lfs] at hℓ1 hℓ2
    rw [Finset.mem_filter] at hℓ1 hℓ2
    obtain ⟨-, hY1non, -, hXY1⟩ := hY1
    obtain ⟨-, hY2non, -, hXY2⟩ := hY2
    obtain ⟨-, hℓhyp, hxℓ, hℓ1Y⟩ := hℓ1
    obtain ⟨-, -, -, hℓ2Y⟩ := hℓ2
    have hℓnotX : ¬ ℓ ⊆ X := by
      intro hsub
      have hsubx : ℓ ⊆ ({x} : Set V) := by
        intro z hz
        have hzX : z ∈ X := hsub hz
        have hzY : z ∈ Y1 := hℓ1Y hz
        have hmem : z ∈ X ∩ Y1 := ⟨hzX, hzY⟩
        rwa [hXY1] at hmem
      obtain ⟨a, b, ha, h4, hℓeq⟩ := hℓhyp
      have hab : a ≠ b := by
        intro h
        rw [h] at h4
        simp at h4
      have ha' : a ∈ ({x} : Set V) := by
        apply hsubx
        rw [hℓeq]
        exact mem_starLine_left ha
      have hb' : b ∈ ({x} : Set V) := by
        apply hsubx
        rw [hℓeq]
        exact mem_starLine_right (color_eq_of_dist_four hP h4 ▸ ha)
      exact hab (by simpa using ha'.trans hb'.symm)
    obtain ⟨W, -, huniq⟩ :=
      existsUnique_tangent hP hT c hdeg hreg hii hX hx hℓhyp hxℓ hℓnotX
    have hY1eq : Y1 = W := huniq Y1 ⟨hY1non.1, hℓ1Y, hXY1⟩
    have hY2eq : Y2 = W := huniq Y2 ⟨hY2non.1, hℓ2Y, hXY2⟩
    exact hne (hY1eq.trans hY2eq.symm)
  have hbiUnion : Lall = Bfs.biUnion Lfs := by
    ext ℓ
    constructor
    · intro hℓ
      rw [Finset.mem_filter] at hℓ
      obtain ⟨-, hℓhyp, hxℓ, hℓnotX⟩ := hℓ
      obtain ⟨W, ⟨hWplane, hℓW, hXW⟩, -⟩ :=
        existsUnique_tangent hP hT c hdeg hreg hii hX hx hℓhyp hxℓ hℓnotX
      have hWne : W ≠ ptPerp Γ c {x} := by
        intro hWperp
        exact not_subset_ptPerp_singleton_of_isHypLine hP hT hx0 hℓhyp hxℓ
          (hWperp ▸ hℓW)
      have hWnon : IsNonabsPlane Γ c W :=
        isNonabsPlane_of_inter_eq_singleton hP hT c hdeg hreg hX hWplane hXW hWne
      have hxW : x ∈ W := hℓW hxℓ
      rw [Finset.mem_biUnion]
      refine ⟨W, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hWnon, hxW, hXW⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hℓhyp, hxℓ, hℓW⟩
    · intro hℓ
      rw [Finset.mem_biUnion] at hℓ
      obtain ⟨Y, hY, hℓY⟩ := hℓ
      rw [Finset.mem_filter] at hY hℓY
      obtain ⟨-, hYnon, hxY, hXY⟩ := hY
      obtain ⟨-, hℓhyp, hxℓ, hℓYsub⟩ := hℓY
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hℓhyp, hxℓ, ?_⟩
      intro hℓX
      have hsubx : ℓ ⊆ ({x} : Set V) := by
        intro z hz
        have hzX : z ∈ X := hℓX hz
        have hzY : z ∈ Y := hℓYsub hz
        have hmem : z ∈ X ∩ Y := ⟨hzX, hzY⟩
        rwa [hXY] at hmem
      obtain ⟨a, b, ha, h4, hℓeq⟩ := hℓhyp
      have hab : a ≠ b := by
        intro h
        rw [h] at h4
        simp at h4
      have ha' : a ∈ ({x} : Set V) := by
        apply hsubx
        rw [hℓeq]
        exact mem_starLine_left ha
      have hb' : b ∈ ({x} : Set V) := by
        apply hsubx
        rw [hℓeq]
        exact mem_starLine_right (color_eq_of_dist_four hP h4 ▸ ha)
      exact hab (by simpa using ha'.trans hb'.symm)
  have hBcard : Bfs.card = s - 1 := by
    have hsum : ∑ Y ∈ Bfs, (Lfs Y).card = Bfs.card * s := by
      rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
    have hLen : Lall.card = ∑ Y ∈ Bfs, (Lfs Y).card := by
      rw [hbiUnion, Finset.card_biUnion hdisj]
    have heq : s ^ 2 - s = Bfs.card * s := by
      rw [← hLallcard, hLen, hsum]
    have hs : 0 < s := by
      have := two_le_s hP hT c hdeg
      omega
    have heq' : Bfs.card * s = (s - 1) * s := by
      rw [heq.symm, Nat.sub_mul, one_mul, pow_two]
    exact Nat.eq_of_mul_eq_mul_right hs heq'
  have hβeq : tangentBundle Γ c X x =
      ({X, ptPerp Γ c {x}} : Set (Set V)) ∪ (Bfs : Set (Set V)) := by
    ext Y
    constructor
    · intro hY
      rw [tangentBundle] at hY
      obtain ⟨hYplane, hYX | hYinter⟩ := hY
      · rw [hYX]
        exact Or.inl (by simp)
      · have hxY : x ∈ Y := by
          have h : x ∈ X ∩ Y := by rw [hYinter]; simp
          exact h.2
        by_cases hYabs : IsAbsPlane Γ c Y
        · obtain ⟨u, hu0, rfl⟩ := hYabs
          have hxY' : x ∈ ptPerp Γ c {u} := hxY
          have hux : Γ.dist x u ≤ 2 := (mem_ptPerp.mp hxY').2 u (by simp)
          by_cases huxeq : u = x
          · rw [huxeq]
            exact Or.inl (by simp)
          · exfalso
            have hxu2 : Γ.dist u x = 2 :=
              dist_eq_two_of_le_two_of_ne (c := c) hP hu0 hx0 huxeq
                (by rw [SimpleGraph.dist_comm]; exact hux)
            have huX : u ∉ X := by
              intro huX
              have h4 : Γ.dist u x = 4 :=
                dist_eq_four_of_mem_of_isOvoid hP hT hX.2 huX hx huxeq
              omega
            have hcount := ncard_inter_ovoid_ptPerp hP hT c hdeg hX.2 hu0 huX
            rw [hYinter] at hcount
            simp at hcount
            have ht := two_le_t hP hT c hdeg
            omega
        · have hYnon : IsNonabsPlane Γ c Y := by
            rcases isStarPlane_cases hP hT c hdeg hreg hYplane with h | h
            · exact absurd h hYabs
            · exact h
          right
          rw [Finset.mem_coe, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hYnon, hxY, hYinter⟩
    · intro hY
      change IsStarPlane Γ c Y ∧ (Y = X ∨ X ∩ Y = {x})
      rcases hY with hY | hY
      · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
        rcases hY with rfl | rfl
        · exact ⟨hX.1, Or.inl rfl⟩
        · exact ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hx0, Or.inr hXint⟩
      · rw [Finset.mem_coe, Finset.mem_filter] at hY
        obtain ⟨-, hYnon, hxY, hXY⟩ := hY
        exact ⟨hYnon.1, Or.inr hXY⟩
  have hdisj2 : Disjoint ({X, ptPerp Γ c {x}} : Set (Set V)) (Bfs : Set (Set V)) := by
    rw [Set.disjoint_left]
    intro Y hY hYB
    rw [Finset.mem_coe, Finset.mem_filter] at hYB
    obtain ⟨-, hYnon, hxY, hXY⟩ := hYB
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    rcases hY with hYX | hYperp
    · rw [hYX] at hXY
      rw [Set.inter_self] at hXY
      have h1 : ({x} : Set V).ncard = s * t + 1 := by
        rw [← hXY]
        exact ncard_of_isOvoid hP hT c hdeg hX.2
      simp at h1
      have ht : 2 ≤ t := two_le_t hP hT c hdeg
      have hst : 2 ≤ s * t := by
        have h4 := Nat.mul_le_mul hs ht
        omega
      omega
    · rw [hYperp] at hYnon
      have h1 : (ptPerp Γ c {x}).ncard = s * t + s + 1 :=
        ncard_ptPerp_singleton hP hT c hdeg hx0
      have h2 : (ptPerp Γ c {x}).ncard = s * t + 1 :=
        ncard_of_isOvoid hP hT c hdeg hYnon.2
      omega
  rw [hβeq, Set.ncard_union_eq hdisj2, Set.ncard_pair hXne, Set.ncard_coe_finset, hBcard]
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  omega

theorem ncard_of_isPlaneBundle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCondPrime Γ c)
    {β : Set (Set V)} (hβ : IsPlaneBundle Γ c β) : β.ncard = s + 1 := by
  classical
  rcases hβ with ⟨L, hL, rfl⟩ | ⟨X, x, hX, hx, rfl⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := hL
    rcases dist_eq_two_or_four_of_color_zero hP ha hb hab with h2 | h4
    · exact ncard_axisBundle_of_dist_two hP hT c hdeg hreg ha hb hab h2
    · exact (ncard_planes_superset_hypLine hP hT c hdeg hreg hii
        (⟨a, b, ha, h4, rfl⟩ : IsHypLine Γ c (starLine Γ c a b))).1
  · exact ncard_tangentBundle hP hT c hdeg hreg hii hX hx

end BundleCardinality

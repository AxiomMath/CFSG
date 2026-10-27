module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Bundles2
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.ConjugateBundles2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section NetsAux

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem isStarLine_ne_singleton {c : Γ.Coloring (Fin 2)} {L : Set V}
    (hL : IsStarLine Γ c L) (x : V) : L ≠ {x} := by
  intro hEq
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hL
  have ha' : a ∈ ({x} : Set V) := hEq ▸ mem_starLine_left ha
  have hb' : b ∈ ({x} : Set V) := hEq ▸ mem_starLine_right hb
  exact hab (by simpa using ha'.trans hb'.symm)

private theorem ptPerp_pair_eq (c : Γ.Coloring (Fin 2)) (x y : V) :
    ptPerp Γ c {x, y} = ptPerp Γ c {x} ∩ ptPerp Γ c {y} := by
  ext z
  rw [Set.mem_inter_iff, mem_ptPerp_pair, mem_ptPerp, mem_ptPerp]
  constructor
  · rintro ⟨h0, hx, hy⟩
    exact ⟨⟨h0, fun a ha => by rw [Set.mem_singleton_iff] at ha; subst ha; exact hx⟩,
      ⟨h0, fun a ha => by rw [Set.mem_singleton_iff] at ha; subst ha; exact hy⟩⟩
  · rintro ⟨⟨h0, hx⟩, -, hy⟩
    exact ⟨h0, hx x (Set.mem_singleton x), hy y (Set.mem_singleton y)⟩

private theorem eq_ptPerp_of_isAbsPlane_of_mem_tangentBundle (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {Z W : Set V} {z : V} (hZ : IsNonabsPlane Γ c Z) (hz : z ∈ Z)
    (hW : W ∈ tangentBundle Γ c Z z) (hWabs : IsAbsPlane Γ c W) :
    W = ptPerp Γ c {z} := by
  classical
  have hz0 : c z = 0 := hZ.1.1.1.1 z hz
  rcases hW.2 with hWZ | hWZ
  · exact absurd (hWZ ▸ hZ) (not_isNonabsPlane_of_isAbsPlane hP hT c hdeg hWabs)
  · obtain ⟨u, hu0, rfl⟩ := hWabs
    have huper : u ∈ ptPerp Γ c {u} := by
      rw [mem_ptPerp]
      exact ⟨hu0, fun y hy => by rw [Set.mem_singleton_iff] at hy; subst hy; simp⟩
    have huZ : u ∈ Z := by
      by_contra huZ
      have hcount := ncard_inter_ovoid_ptPerp hP hT c hdeg hZ.2 hu0 huZ
      rw [hWZ] at hcount
      simp at hcount
      have ht : 2 ≤ t := two_le_t hP hT c hdeg
      omega
    have huz : u = z := by
      have hmem : u ∈ Z ∩ ptPerp Γ c {u} := ⟨huZ, huper⟩
      rw [hWZ] at hmem
      simpa using hmem
    rw [huz]

end NetsAux

section ConjE

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem inter_inter_eq_empty (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {X X' X'' : Set V} (hX : IsStarPlane Γ c X) (hX' : IsNonabsPlane Γ c X')
    (hX'' : IsStarPlane Γ c X'') (hc : IsConjPlane Γ c X' X) (hc'' : IsConjPlane Γ c X' X'')
    (h : (X ∩ X'').ncard = t + 1) : X ∩ X' ∩ X'' = ∅ := by
  classical
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  rcases isStarPlane_cases hP hT c hdeg hreg hX with hXabs | hXnon
  ·
    obtain ⟨w, hw0, rfl⟩ := hXabs
    have hwX' : w ∈ X' := by
      have hmem : ptPerp Γ c {w} ∈ conjNet Γ c X' :=
        ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hw0, hc⟩
      exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hX'.1 hw0).mp hmem
    have hInter : ptPerp Γ c {w} ∩ X' = {w} := by
      rw [Set.inter_comm]
      exact inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hX' hwX'
    by_contra hne
    obtain ⟨z, hz1, hz2⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hzw : z = w := by
      have hmem : z ∈ ptPerp Γ c {w} ∩ X' := ⟨hz1.1, hz1.2⟩
      rwa [hInter] at hmem
    rw [hzw] at hz2
    rcases isStarPlane_cases hP hT c hdeg hreg hX'' with hX''abs | hX''non
    ·
      obtain ⟨w', hw'0, rfl⟩ := hX''abs
      have hw'X' : w' ∈ X' := by
        have hmem : ptPerp Γ c {w'} ∈ conjNet Γ c X' :=
          ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hw'0, hc''⟩
        exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hX'.1 hw'0).mp hmem
      have hInter' : ptPerp Γ c {w'} ∩ X' = {w'} := by
        rw [Set.inter_comm]
        exact inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hX' hw'X'
      have hww' : w = w' := by
        have hmem : w ∈ ptPerp Γ c {w'} ∩ X' := ⟨hz2, hwX'⟩
        rwa [hInter'] at hmem
      have h1 : (ptPerp Γ c {w}).ncard = s * t + s + 1 :=
        ncard_ptPerp_singleton hP hT c hdeg hw0
      have h2 : (ptPerp Γ c {w}).ncard = t + 1 := by
        rw [← hww'] at h
        simpa using h
      have hs : 2 ≤ s := two_le_s hP hT c hdeg
      have ht' : 2 ≤ t := two_le_t hP hT c hdeg
      nlinarith
    ·
      have hInter'' : ptPerp Γ c {w} ∩ X'' = {w} := by
        rw [Set.inter_comm]
        exact inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hX''non hz2
      have h2 : (ptPerp Γ c {w} ∩ X'').ncard = t + 1 := h
      rw [hInter''] at h2
      simp at h2
      omega
  · rcases isStarPlane_cases hP hT c hdeg hreg hX'' with hX''abs | hX''non
    ·
      obtain ⟨w', hw'0, rfl⟩ := hX''abs
      have hw'X' : w' ∈ X' := by
        have hmem : ptPerp Γ c {w'} ∈ conjNet Γ c X' :=
          ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hw'0, hc''⟩
        exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hX'.1 hw'0).mp hmem
      have hInter : ptPerp Γ c {w'} ∩ X' = {w'} := by
        rw [Set.inter_comm]
        exact inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hX' hw'X'
      by_contra hne
      obtain ⟨z, hz1, hz2⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have hzw : z = w' := by
        have hmem : z ∈ ptPerp Γ c {w'} ∩ X' := ⟨hz2, hz1.2⟩
        rwa [hInter] at hmem
      rw [hzw] at hz1
      have hXint : X ∩ ptPerp Γ c {w'} = {w'} :=
        inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hXnon hz1.1
      have h2 : (X ∩ ptPerp Γ c {w'}).ncard = t + 1 := h
      rw [hXint] at h2
      simp at h2
      omega
    ·
      have hne : X ≠ X'' := by
        intro hEq
        have h1 : X.ncard = s * t + 1 := ncard_of_isOvoid hP hT c hdeg hXnon.2
        have h2 : X.ncard = t + 1 := by
          have h' : (X ∩ X).ncard = t + 1 := hEq.symm ▸ h
          simpa using h'
        have hs : 2 ≤ s := two_le_s hP hT c hdeg
        have ht' : 2 ≤ t := two_le_t hP hT c hdeg
        nlinarith
      have hRstar : IsStarLine Γ c (X ∩ X'') := by
        rcases inter_cases hP hT c hdeg hreg hXnon.1 hX'' hne with hemp | ⟨u, hu⟩ | hline
        · rw [hemp, Set.ncard_empty] at h; omega
        · rw [hu, Set.ncard_singleton] at h; omega
        · exact hline
      by_contra hne'
      obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne'
      have hzR : z ∈ X ∩ X'' := ⟨hz.1.1, hz.2⟩
      have hzX' : z ∈ X' := hz.1.2
      by_cases hsub : X ∩ X'' ⊆ X'
      ·
        rcases eq_or_inter_eq_singleton_of_isConjPlane hP hT c hdeg hreg hst hii hX' hXnon
          hX''non hzX' hzR.1 hzR.2 hc hc'' with hEq | hsingle
        · exact hne hEq
        · rw [hsingle] at h
          simp at h
          omega
      ·
        have hRc : ¬ ptPerp Γ c (X ∩ X'') ⊆ X' := by
          intro hper
          have hdisj : Disjoint (X ∩ X'') X' :=
            disjoint_of_ptPerp_subset hP hT c hdeg hreg hX' hRstar hper
          exact (Set.disjoint_left.mp hdisj) hzR hzX'
        obtain ⟨Y, ⟨-, hRY, hYconj⟩, huniq⟩ :=
          existsUnique_conjPlane_superset hP hT c hdeg hreg hii hX'.1 hRstar hsub hRc
        have hXeq : X = Y := huniq X ⟨hXnon.1, Set.inter_subset_left, hc⟩
        have hX''eq : X'' = Y := huniq X'' ⟨hX'', Set.inter_subset_right, hc''⟩
        exact hne (hXeq.trans hX''eq.symm)

theorem mem_conjBundle_of_two (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {β : Set (Set V)} (hβ : IsPlaneBundle Γ c β) {X₁ X₂ Y : Set V} (h1 : X₁ ∈ β) (h2 : X₂ ∈ β)
    (h12 : X₁ ≠ X₂) (hY : IsStarPlane Γ c Y) (hc1 : IsConjPlane Γ c Y X₁)
    (hc2 : IsConjPlane Γ c Y X₂) : Y ∈ conjBundle Γ c β := by
  classical
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have hii' : TalliniCondPrime Γ c := talliniCondPrime_of_talliniCond hP hT c hdeg hreg hii
  rcases hβ with ⟨L, hL, rfl⟩ | ⟨Z, z, hZ, hz, rfl⟩
  ·
    have hL1 : L ⊆ X₁ := h1.2
    have hL2 : L ⊆ X₂ := h2.2
    have hInter : X₁ ∩ X₂ = L := inter_eq_of_mem_axisBundle hP hT c hdeg hreg hL h1 h2 h12
    rw [conjBundle_axisBundle hP hT c hdeg hreg hL]
    refine ⟨hY, ?_⟩
    rcases isStarPlane_cases hP hT c hdeg hreg h1.1 with hX₁abs | hX₁non
    · obtain ⟨x₁, hx₁0, rfl⟩ := hX₁abs
      rcases isStarPlane_cases hP hT c hdeg hreg h2.1 with hX₂abs | hX₂non
      ·
        obtain ⟨x₂, hx₂0, rfl⟩ := hX₂abs
        have hx₁Y : x₁ ∈ Y := by
          have hmem : ptPerp Γ c {x₁} ∈ conjNet Γ c Y :=
            ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hx₁0, hc1⟩
          exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hY hx₁0).mp hmem
        have hx₂Y : x₂ ∈ Y := by
          have hmem : ptPerp Γ c {x₂} ∈ conjNet Γ c Y :=
            ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hx₂0, hc2⟩
          exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hY hx₂0).mp hmem
        have hx₁₂ : x₁ ≠ x₂ := by
          intro h
          exact h12 (by rw [h])
        have hLpair : L = ptPerp Γ c {x₁, x₂} := by
          rw [← hInter, ptPerp_pair_eq]
        intro w hw
        rw [hLpair] at hw
        exact hY.1.1.2 x₁ hx₁Y x₂ hx₂Y hx₁₂ hw
      ·
        have hx₁Y : x₁ ∈ Y := by
          have hmem : ptPerp Γ c {x₁} ∈ conjNet Γ c Y :=
            ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hx₁0, hc1⟩
          exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hY hx₁0).mp hmem
        have hx₁X₂ : x₁ ∉ X₂ := by
          intro hmem
          have hsingle : L = {x₁} := by
            rw [← hInter, Set.inter_comm]
            exact inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hX₂non hmem
          exact isStarLine_ne_singleton hL x₁ hsingle
        have hconj : conjLine Γ c X₂ x₁ ⊆ Y :=
          subset_of_isConjPlane hP hT c hdeg hreg hii hX₂non.1 hY
            ((isConjPlane_comm hP hT c hdeg hreg).mp hc2) hx₁Y hx₁X₂
        intro w hw
        have hw' : w ∈ conjLine Γ c X₂ x₁ := by
          show w ∈ ptPerp Γ c (ptPerp Γ c {x₁} ∩ X₂)
          rw [hInter]
          exact hw
        exact hconj hw'
    · rcases isStarPlane_cases hP hT c hdeg hreg h2.1 with hX₂abs | hX₂non
      ·
        obtain ⟨x₂, hx₂0, rfl⟩ := hX₂abs
        have hx₂Y : x₂ ∈ Y := by
          have hmem : ptPerp Γ c {x₂} ∈ conjNet Γ c Y :=
            ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hx₂0, hc2⟩
          exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hY hx₂0).mp hmem
        have hx₂X₁ : x₂ ∉ X₁ := by
          intro hmem
          have hsingle : L = {x₂} := by
            rw [← hInter]
            exact inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hX₁non hmem
          exact isStarLine_ne_singleton hL x₂ hsingle
        have hconj : conjLine Γ c X₁ x₂ ⊆ Y :=
          subset_of_isConjPlane hP hT c hdeg hreg hii hX₁non.1 hY
            ((isConjPlane_comm hP hT c hdeg hreg).mp hc1) hx₂Y hx₂X₁
        intro w hw
        have hw' : w ∈ conjLine Γ c X₁ x₂ := by
          show w ∈ ptPerp Γ c (ptPerp Γ c {x₂} ∩ X₁)
          rw [Set.inter_comm (ptPerp Γ c {x₂}) X₁, hInter]
          exact hw
        exact hconj hw'
      ·
        rcases isStarPlane_cases hP hT c hdeg hreg hY with hYabs | hYnon
        ·
          obtain ⟨u, hu0, rfl⟩ := hYabs
          have huX₁ : u ∈ X₁ := by
            have hmem : ptPerp Γ c {u} ∈ conjNet Γ c X₁ :=
              ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hu0,
                (isConjPlane_comm hP hT c hdeg hreg).mp hc1⟩
            exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hX₁non.1 hu0).mp hmem
          have huX₂ : u ∈ X₂ := by
            have hmem : ptPerp Γ c {u} ∈ conjNet Γ c X₂ :=
              ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hu0,
                (isConjPlane_comm hP hT c hdeg hreg).mp hc2⟩
            exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hX₂non.1 hu0).mp hmem
          have huL : u ∈ L := by rw [← hInter]; exact ⟨huX₁, huX₂⟩
          intro w hw
          rw [mem_ptPerp] at hw ⊢
          exact ⟨hw.1, fun y hy => by
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
            exact hw.2 u huL⟩
        ·
          have hLhyp : IsHypLine Γ c L :=
            isHypLine_of_isStarLine_subset_of_isNonabsPlane hP hT hX₁non hL hL1
          have hLcard : L.ncard = t + 1 := IsHypLine.ncard hP hT c hdeg hreg hLhyp
          have hIntercard : (X₁ ∩ X₂).ncard = t + 1 := by
            rw [hInter]; exact hLcard
          have he1 : X₁ ∩ Y ∩ X₂ = ∅ :=
            inter_inter_eq_empty hP hT c hdeg hreg hst hii hX₁non.1 hYnon hX₂non.1 hc1 hc2
              hIntercard
          have hLtwo : 1 < L.ncard := by rw [hLcard]; omega
          obtain ⟨a, haL, b, hbL, hab⟩ := (Set.one_lt_ncard (s := L)).mp hLtwo
          have haX₁ : a ∈ X₁ := hL1 haL
          have haX₂ : a ∈ X₂ := hL2 haL
          have haY : a ∉ Y := by
            intro hmem
            have hmem' : a ∈ X₁ ∩ Y ∩ X₂ := ⟨⟨haX₁, hmem⟩, haX₂⟩
            rw [he1] at hmem'
            exact hmem'
          have ha0' : c a = 0 := color_zero_of_mem_isStarLine hL haL
          have hper₁ : conjLine Γ c Y a ⊆ X₁ :=
            subset_of_isConjPlane hP hT c hdeg hreg hii hYnon.1 hX₁non.1 hc1 haX₁ haY
          have hper₂ : conjLine Γ c Y a ⊆ X₂ :=
            subset_of_isConjPlane hP hT c hdeg hreg hii hYnon.1 hX₂non.1 hc2 haX₂ haY
          have hperL : conjLine Γ c Y a ⊆ L := by
            rw [← hInter]
            exact fun w hw => ⟨hper₁ hw, hper₂ hw⟩
          have hNhyp : IsHypLine Γ c (conjLine Γ c Y a) :=
            (isHypLine_conjLine hP hT c hdeg hreg hYnon.1 ha0' haY).1
          have hNstar : IsStarLine Γ c (conjLine Γ c Y a) := IsHypLine.isStarLine hP hNhyp
          have hNeq : conjLine Γ c Y a = L := eq_of_isStarLine_subset hP hT hNstar hL hperL
          have hperp : ptPerp Γ c (conjLine Γ c Y a) ⊆ Y :=
            (isHypLine_conjLine hP hT c hdeg hreg hYnon.1 ha0' haY).2.2
          rwa [hNeq] at hperp
  ·
    have hInter : X₁ ∩ X₂ = {z} :=
      inter_eq_of_mem_tangentBundle hP hT c hdeg hreg hii' hZ hz h1 h2 h12
    have hz0 : c z = 0 := hZ.1.1.1.1 z hz
    have hzmem : z ∈ X₁ ∩ X₂ := by rw [hInter]; exact Set.mem_singleton z
    have hzX₁ : z ∈ X₁ := hzmem.1
    have hzX₂ : z ∈ X₂ := hzmem.2
    have hex : ∃ W, (W = X₁ ∨ W = X₂) ∧ IsNonabsPlane Γ c W := by
      by_cases h1n : IsNonabsPlane Γ c X₁
      · exact ⟨X₁, Or.inl rfl, h1n⟩
      · have h1abs : IsAbsPlane Γ c X₁ := by
          rcases isStarPlane_cases hP hT c hdeg hreg h1.1 with h | h
          · exact h
          · exact absurd h h1n
        have h1eq : X₁ = ptPerp Γ c {z} :=
          eq_ptPerp_of_isAbsPlane_of_mem_tangentBundle hP hT c hdeg hZ hz h1 h1abs
        refine ⟨X₂, Or.inr rfl, ?_⟩
        by_contra h2n
        have h2abs : IsAbsPlane Γ c X₂ := by
          rcases isStarPlane_cases hP hT c hdeg hreg h2.1 with h | h
          · exact h
          · exact absurd h h2n
        have h2eq : X₂ = ptPerp Γ c {z} :=
          eq_ptPerp_of_isAbsPlane_of_mem_tangentBundle hP hT c hdeg hZ hz h2 h2abs
        exact h12 (h1eq.trans h2eq.symm)
    obtain ⟨W, hW12, hWnon⟩ := hex
    have hWβ : W ∈ tangentBundle Γ c Z z := by
      rcases hW12 with rfl | rfl
      · exact h1
      · exact h2
    have hzW : z ∈ W := by
      rcases hWβ.2 with h | h
      · rw [h]; exact hz
      · have hmem : z ∈ Z ∩ W := by rw [h]; exact Set.mem_singleton z
        exact hmem.2
    have hWY : IsConjPlane Γ c W Y := by
      rcases hW12 with rfl | rfl
      · exact (isConjPlane_comm hP hT c hdeg hreg).mp hc1
      · exact (isConjPlane_comm hP hT c hdeg hreg).mp hc2
    have hzY : z ∈ Y := by
      rcases isStarPlane_cases hP hT c hdeg hreg hY with hYabs | hYnon
      · obtain ⟨u, hu0, rfl⟩ := hYabs
        have huX₁ : u ∈ X₁ := by
          have hmem : ptPerp Γ c {u} ∈ conjNet Γ c X₁ :=
            ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hu0,
              (isConjPlane_comm hP hT c hdeg hreg).mp hc1⟩
          exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg h1.1 hu0).mp hmem
        have huX₂ : u ∈ X₂ := by
          have hmem : ptPerp Γ c {u} ∈ conjNet Γ c X₂ :=
            ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hu0,
              (isConjPlane_comm hP hT c hdeg hreg).mp hc2⟩
          exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg h2.1 hu0).mp hmem
        have huz : u = z := by
          have hmem : u ∈ X₁ ∩ X₂ := ⟨huX₁, huX₂⟩
          rw [hInter] at hmem
          simpa using hmem
        rw [huz, mem_ptPerp]
        exact ⟨hz0, fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; simp⟩
      · by_contra hzY'
        have hper₁ : conjLine Γ c Y z ⊆ X₁ :=
          subset_of_isConjPlane hP hT c hdeg hreg hii hYnon.1 h1.1 hc1 hzX₁ hzY'
        have hper₂ : conjLine Γ c Y z ⊆ X₂ :=
          subset_of_isConjPlane hP hT c hdeg hreg hii hYnon.1 h2.1 hc2 hzX₂ hzY'
        have hsub : conjLine Γ c Y z ⊆ ({z} : Set V) := by
          rw [← hInter]
          exact fun w hw => ⟨hper₁ hw, hper₂ hw⟩
        have hNhyp : IsHypLine Γ c (conjLine Γ c Y z) :=
          (isHypLine_conjLine hP hT c hdeg hreg hYnon.1 hz0 hzY').1
        have hNcard : (conjLine Γ c Y z).ncard = t + 1 :=
          IsHypLine.ncard hP hT c hdeg hreg hNhyp
        have hle : (conjLine Γ c Y z).ncard ≤ 1 := by
          have h' := Set.ncard_le_ncard hsub
          simpa using h'
        omega
    obtain ⟨hmain, -⟩ := conjBundle_tangentBundle hP hT c hdeg hreg hst hii hWnon hzW
    rw [← tangentBundle_eq hP hT c hdeg hreg hii' hZ hz hWβ hWnon]
    rw [hmain]
    exact ⟨hY, hzY, hWY⟩

theorem conjNet_inter_conjNet (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {β : Set (Set V)} (hβ : IsPlaneBundle Γ c β) {X Y : Set V} (hX : X ∈ β) (hY : Y ∈ β)
    (hXY : X ≠ Y) : conjNet Γ c X ∩ conjNet Γ c Y = conjBundle Γ c β := by
  classical
  ext Z
  constructor
  · rintro ⟨hZX, hZY⟩
    exact mem_conjBundle_of_two hP hT c hdeg hreg hst hii hβ hX hY hXY hZX.1
      ((isConjPlane_comm hP hT c hdeg hreg).mp hZX.2)
      ((isConjPlane_comm hP hT c hdeg hreg).mp hZY.2)
  · rintro ⟨hZplane, hZall⟩
    exact ⟨⟨hZplane, (isConjPlane_comm hP hT c hdeg hreg).mp (hZall X hX)⟩,
      ⟨hZplane, (isConjPlane_comm hP hT c hdeg hreg).mp (hZall Y hY)⟩⟩

end ConjE

section ConjE'

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem exists_mem_conjNet_of_not_mem (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {β : Set (Set V)} (hβ : IsPlaneBundle Γ c β) {X : Set V} (hX : IsStarPlane Γ c X) {p : V}
    (hpβ : ∀ Y ∈ β, p ∈ Y) (hpX : p ∉ X) : ∃ Y ∈ β, Y ∈ conjNet Γ c X := by
  classical
  have hii' : TalliniCondPrime Γ c := talliniCondPrime_of_talliniCond hP hT c hdeg hreg hii
  have hβcard : β.ncard = s + 1 := ncard_of_isPlaneBundle hP hT c hdeg hreg hst hii' hβ
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have hβtwo : 1 < β.ncard := by rw [hβcard]; omega
  obtain ⟨W₁, hW₁, W₂, hW₂, hW₁₂⟩ := (Set.one_lt_ncard (s := β)).mp hβtwo
  rcases hβ with ⟨L, hL, rfl⟩ | ⟨Z, z, hZ, hz, rfl⟩
  ·
    have hpL : p ∈ L := by
      have hp₁ : p ∈ W₁ := hpβ W₁ hW₁
      have hp₂ : p ∈ W₂ := hpβ W₂ hW₂
      have hinter : W₁ ∩ W₂ = L :=
        inter_eq_of_mem_axisBundle hP hT c hdeg hreg hL hW₁ hW₂ hW₁₂
      rw [← hinter]
      exact ⟨hp₁, hp₂⟩
    have hp0 : c p = 0 := color_zero_of_mem_isStarLine hL hpL
    have hpN : p ∈ conjLine Γ c X p :=
      (isHypLine_conjLine hP hT c hdeg hreg hX hp0 hpX).2.1
    have hNhyp : IsHypLine Γ c (conjLine Γ c X p) :=
      (isHypLine_conjLine hP hT c hdeg hreg hX hp0 hpX).1
    have hNstar : IsStarLine Γ c (conjLine Γ c X p) := IsHypLine.isStarLine hP hNhyp
    by_cases hNL : conjLine Γ c X p = L
    · refine ⟨W₁, hW₁, mem_conjNet_of_conjLine_subset hP hT c hdeg hreg hX hp0 hpX hW₁.1 ?_⟩
      rw [hNL]
      exact hW₁.2
    ·
      obtain ⟨q, hqN, hqp⟩ := exists_mem_ne_of_isStarLine hNstar p
      obtain ⟨r, hrL, hrp⟩ := exists_mem_ne_of_isStarLine hL p
      have hnc : ¬ IsStarCollinear Γ c p q r := by
        rintro ⟨S, hS, hpS, hqS, hrS⟩
        have hSN : S = conjLine Γ c X p := by
          have h1 : S = starLine Γ c p q :=
            starLine_eq_of_isStarLine_of_mem hP hT hS hpS hqS hqp.symm
          have h2 : conjLine Γ c X p = starLine Γ c p q :=
            starLine_eq_of_isStarLine_of_mem hP hT hNstar hpN hqN (Ne.symm hqp)
          rw [h1, ← h2]
        have hrN : r ∈ conjLine Γ c X p := by rw [← hSN]; exact hrS
        have hNL' : conjLine Γ c X p = L := by
          rw [starLine_eq_of_isStarLine_of_mem hP hT hNstar hpN hrN (Ne.symm hrp),
            ← starLine_eq_of_isStarLine_of_mem hP hT hL hpL hrL (Ne.symm hrp)]
        exact hNL hNL'
      have hq0 : c q = 0 := color_zero_of_mem_isStarLine hNstar hqN
      have hr0 : c r = 0 := color_zero_of_mem_isStarLine hL hrL
      obtain ⟨Y, hYplane, hpY, hqY, hrY⟩ := hii' p q r hp0 hq0 hr0 hnc
      have hLY : L ⊆ Y := by
        have hLpr : L = starLine Γ c p r :=
          starLine_eq_of_isStarLine_of_mem hP hT hL hpL hrL (Ne.symm hrp)
        rw [hLpr]
        exact hYplane.1.1.2 p hpY r hrY (Ne.symm hrp)
      have hNY : conjLine Γ c X p ⊆ Y := by
        have hNpq : conjLine Γ c X p = starLine Γ c p q :=
          starLine_eq_of_isStarLine_of_mem hP hT hNstar hpN hqN (Ne.symm hqp)
        rw [hNpq]
        exact hYplane.1.1.2 p hpY q hqY (Ne.symm hqp)
      exact ⟨Y, ⟨hYplane, hLY⟩,
        mem_conjNet_of_conjLine_subset hP hT c hdeg hreg hX hp0 hpX hYplane hNY⟩
  ·
    have hinter : W₁ ∩ W₂ = {z} :=
      inter_eq_of_mem_tangentBundle hP hT c hdeg hreg hii' hZ hz hW₁ hW₂ hW₁₂
    have hpz : p = z := by
      have hp₁ : p ∈ W₁ := hpβ W₁ hW₁
      have hp₂ : p ∈ W₂ := hpβ W₂ hW₂
      have hmem : p ∈ ({z} : Set V) := by rw [← hinter]; exact ⟨hp₁, hp₂⟩
      simpa using hmem
    have hp0 : c p = 0 := by rw [hpz]; exact hZ.1.1.1.1 z hz
    have hpN : p ∈ conjLine Γ c X p :=
      (isHypLine_conjLine hP hT c hdeg hreg hX hp0 hpX).2.1
    have hNhyp : IsHypLine Γ c (conjLine Γ c X p) :=
      (isHypLine_conjLine hP hT c hdeg hreg hX hp0 hpX).1
    have hNstar : IsStarLine Γ c (conjLine Γ c X p) := IsHypLine.isStarLine hP hNhyp
    obtain ⟨q, hqN, hqp⟩ := exists_mem_ne_of_isStarLine hNstar p
    have hq0 : c q = 0 := color_zero_of_mem_isStarLine hNstar hqN
    have hex : ∃ W ∈ tangentBundle Γ c Z z, q ∉ W := by
      by_contra h
      push Not at h
      have hq₁ : q ∈ W₁ := h W₁ hW₁
      have hq₂ : q ∈ W₂ := h W₂ hW₂
      have hmem : q ∈ ({z} : Set V) := by rw [← hinter]; exact ⟨hq₁, hq₂⟩
      have hqz : q = z := by simpa using hmem
      exact hqp (hqz.trans hpz.symm)
    obtain ⟨W, hW, -⟩ :=
      existsUnique_mem_of_isPlaneBundle hP hT c hdeg hreg hst hii' (Or.inr ⟨Z, z, hZ, hz, rfl⟩)
        hq0 hex
    have hWβ : W ∈ tangentBundle Γ c Z z := hW.1
    have hqW : q ∈ W := hW.2
    have hpW : p ∈ W := hpβ W hWβ
    have hNW : conjLine Γ c X p ⊆ W := by
      have hNpq : conjLine Γ c X p = starLine Γ c p q :=
        starLine_eq_of_isStarLine_of_mem hP hT hNstar hpN hqN (Ne.symm hqp)
      rw [hNpq]
      exact hWβ.1.1.1.2 p hpW q hqW (Ne.symm hqp)
    exact ⟨W, hWβ, mem_conjNet_of_conjLine_subset hP hT c hdeg hreg hX hp0 hpX hWβ.1 hNW⟩

end ConjE'

section ConjE4

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ncard_inter_conjNet (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {β : Set (Set V)} (hβ : IsPlaneBundle Γ c β) {X : Set V} (hX : IsStarPlane Γ c X)
    (hXβ : X ∉ conjBundle Γ c β) : (β ∩ conjNet Γ c X).ncard = 1 := by
  classical
  have hii' : TalliniCondPrime Γ c := talliniCondPrime_of_talliniCond hP hT c hdeg hreg hii
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  rcases hβ with ⟨L, hL, rfl⟩ | ⟨Z, z, hZ, hz, rfl⟩
  ·
    have hβL : IsPlaneBundle Γ c (axisBundle Γ c L) := Or.inl ⟨L, hL, rfl⟩
    have hex : ∃ Y, Y ∈ axisBundle Γ c L ∧ Y ∈ conjNet Γ c X := by
      by_cases hq : ∃ q ∈ L, q ∉ X
      · obtain ⟨q, hqL, hqX⟩ := hq
        obtain ⟨Y, hYβ, hYnet⟩ :=
          exists_mem_conjNet_of_not_mem hP hT c hdeg hreg hst hii hβL hX
            (fun Y hY => hY.2 hqL) hqX
        exact ⟨Y, hYβ, hYnet⟩
      · push Not at hq
        rcases isStarPlane_cases hP hT c hdeg hreg hX with hXabs | hXnon
        ·
          obtain ⟨u, hu0, rfl⟩ := hXabs
          have hstar : IsStarPlane Γ c (ptPerp Γ c {u}) :=
            isStarPlane_ptPerp_singleton hP hT c hdeg hu0
          exact ⟨ptPerp Γ c {u}, ⟨hstar, hq⟩,
            hstar, (isConjPlane_self_iff hP hT c hdeg hreg hstar).mpr ⟨u, hu0, rfl⟩⟩
        ·
          have hLhyp : IsHypLine Γ c L :=
            isHypLine_of_isStarLine_subset_of_isNonabsPlane hP hT hXnon hL hq
          have hLcard : L.ncard = t + 1 := IsHypLine.ncard hP hT c hdeg hreg hLhyp
          have hLtwo : 1 < L.ncard := by rw [hLcard]; omega
          obtain ⟨y, hyL, z₀, hzL, hyz⟩ := (Set.one_lt_ncard (s := L)).mp hLtwo
          have hyX : y ∈ X := hq y hyL
          have hz₀0 : c z₀ = 0 := color_zero_of_mem_isStarLine hL hzL
          have hstar : IsStarPlane Γ c (ptPerp Γ c {z₀}) :=
            isStarPlane_ptPerp_singleton hP hT c hdeg hz₀0
          obtain ⟨hmain, X', hX'non, hyX', hγeq⟩ :=
            conjBundle_tangentBundle hP hT c hdeg hreg hst hii hXnon hyX
          have hγbund : IsPlaneBundle Γ c (conjBundle Γ c (tangentBundle Γ c X y)) :=
            Or.inr ⟨X', y, hX'non, hyX', hγeq⟩
          have hγall : ∀ W ∈ conjBundle Γ c (tangentBundle Γ c X y), y ∈ W := by
            intro W hW
            rw [hmain] at hW
            exact hW.2.1
          have hyperp : y ∉ ptPerp Γ c {z₀} := by
            intro hyz'
            have hle : Γ.dist y z₀ ≤ 2 := (mem_ptPerp.mp hyz').2 z₀ (Set.mem_singleton z₀)
            have h4 : Γ.dist y z₀ = 4 := IsHypLine.dist_eq_four hP hT hLhyp hyL hzL hyz
            omega
          obtain ⟨W, hWγ, hWnet⟩ :=
            exists_mem_conjNet_of_not_mem hP hT c hdeg hreg hst hii hγbund hstar hγall hyperp
          rw [conjNet_ptPerp hP hT c hdeg hreg hz₀0] at hWnet
          have hWy : y ∈ W := hγall W hWγ
          have hWz : z₀ ∈ W := hWnet.2
          rw [hmain] at hWγ
          have hWconj : IsConjPlane Γ c X W := hWγ.2.2
          have hLW : L ⊆ W := by
            have hLyz : L = starLine Γ c y z₀ :=
              starLine_eq_of_isStarLine_of_mem hP hT hL hyL hzL hyz
            rw [hLyz]
            exact hWnet.1.1.1.2 y hWy z₀ hWz hyz
          exact ⟨W, ⟨hWnet.1, hLW⟩, ⟨hWnet.1, hWconj⟩⟩
    obtain ⟨Y, hYβ, hYnet⟩ := hex
    have hmem : Y ∈ axisBundle Γ c L ∩ conjNet Γ c X := ⟨hYβ, hYnet⟩
    have hpos : 0 < (axisBundle Γ c L ∩ conjNet Γ c X).ncard :=
      (Set.ncard_pos (s := axisBundle Γ c L ∩ conjNet Γ c X)).mpr ⟨Y, hmem⟩
    refine le_antisymm ?_ (Nat.succ_le_of_lt hpos)
    have hsub : axisBundle Γ c L ∩ conjNet Γ c X ⊆ ({Y} : Set (Set V)) := by
      rintro W ⟨hWβ, hWnet⟩
      rw [Set.mem_singleton_iff]
      by_contra hWY
      exact hXβ (mem_conjBundle_of_two hP hT c hdeg hreg hst hii hβL hYβ hWβ
        (Ne.symm hWY) hX hYnet.2 hWnet.2)
    have hle := Set.ncard_le_ncard hsub
    simpa using hle
  ·
    have hztangent : ∀ Y ∈ tangentBundle Γ c Z z, z ∈ Y := by
      intro Y hY
      rcases hY.2 with h | h
      · rw [h]; exact hz
      · have hmem : z ∈ Z ∩ Y := by rw [h]; exact Set.mem_singleton z
        exact hmem.2
    have hex : ∃ Y, Y ∈ tangentBundle Γ c Z z ∧ Y ∈ conjNet Γ c X := by
      by_cases hzX : z ∈ X
      · refine ⟨ptPerp Γ c {z}, ?_, ?_⟩
        · exact ⟨isStarPlane_ptPerp_singleton hP hT c hdeg (hZ.1.1.1.1 z hz),
            Or.inr (inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hZ hz)⟩
        · exact ⟨isStarPlane_ptPerp_singleton hP hT c hdeg (hZ.1.1.1.1 z hz),
            ((ptPerp_mem_conjNet_iff hP hT c hdeg hreg hX (hZ.1.1.1.1 z hz)).mpr hzX).2⟩
      · obtain ⟨Y, hYβ, hYnet⟩ :=
          exists_mem_conjNet_of_not_mem hP hT c hdeg hreg hst hii
            (Or.inr ⟨Z, z, hZ, hz, rfl⟩) hX hztangent hzX
        exact ⟨Y, hYβ, hYnet⟩
    obtain ⟨Y, hYβ, hYnet⟩ := hex
    have hmem : Y ∈ tangentBundle Γ c Z z ∩ conjNet Γ c X := ⟨hYβ, hYnet⟩
    have hpos : 0 < (tangentBundle Γ c Z z ∩ conjNet Γ c X).ncard :=
      (Set.ncard_pos (s := tangentBundle Γ c Z z ∩ conjNet Γ c X)).mpr ⟨Y, hmem⟩
    refine le_antisymm ?_ (Nat.succ_le_of_lt hpos)
    have hsub : tangentBundle Γ c Z z ∩ conjNet Γ c X ⊆ ({Y} : Set (Set V)) := by
      rintro W ⟨hWβ, hWnet⟩
      rw [Set.mem_singleton_iff]
      by_contra hWY
      exact hXβ (mem_conjBundle_of_two hP hT c hdeg hreg hst hii
        (Or.inr ⟨Z, z, hZ, hz, rfl⟩) hYβ hWβ (Ne.symm hWY) hX hYnet.2 hWnet.2)
    have hle := Set.ncard_le_ncard hsub
    simpa using hle

end ConjE4

end CFSG.Geometry.GeneralizedQuadrangles

module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Bundles

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section BundlePoint

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem existsUnique_mem_of_isPlaneBundle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCondPrime Γ c)
    {β : Set (Set V)} (hβ : IsPlaneBundle Γ c β) {p : V} (hp : c p = 0)
    (hpβ : ∃ X ∈ β, p ∉ X) : ∃! X, X ∈ β ∧ p ∈ X := by
  classical
  rcases hβ with ⟨L, hL, rfl⟩ | ⟨X, x, hX, hx, rfl⟩
  ·
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hL
    have haL : a ∈ starLine Γ c a b := mem_starLine_left ha
    have hbL : b ∈ starLine Γ c a b := mem_starLine_right hb
    have hLstar : IsStarLine Γ c (starLine Γ c a b) := isStarLine_starLine ha hb hab
    have hpL : p ∉ starLine Γ c a b := by
      obtain ⟨Z, hZβ, hpZ⟩ := hpβ
      exact fun hpL' => hpZ (hZβ.2 hpL')
    have hnc : ¬ IsStarCollinear Γ c a b p := by
      rintro ⟨W, hW, haW, hbW, hpW⟩
      have hWeq : starLine Γ c a b = W :=
        (starLine_eq_of_isStarLine_of_mem hP hT hW haW hbW hab).symm
      exact hpL (hWeq ▸ hpW)
    obtain ⟨Z, hZplane, haZ, hbZ, hpZ⟩ := hii a b p ha hb hp hnc
    have hLZ : starLine Γ c a b ⊆ Z := by
      intro w hw
      exact hZplane.1.1.2 a haZ b hbZ hab hw
    refine ⟨Z, ⟨⟨hZplane, hLZ⟩, hpZ⟩, ?_⟩
    rintro W ⟨⟨hWplane, hLW⟩, hpW⟩
    by_contra hWZ
    have hinter := inter_eq_of_mem_axisBundle hP hT c hdeg hreg hLstar
      (X := W) (Y := Z) ⟨hWplane, hLW⟩ ⟨hZplane, hLZ⟩ hWZ
    have hpint : p ∈ W ∩ Z := ⟨hpW, hpZ⟩
    rw [hinter] at hpint
    exact hpL hpint
  ·
    have hxmem : ∀ Z ∈ tangentBundle Γ c X x, x ∈ Z := by
      intro Z hZ
      rcases hZ.2 with hZX | hZX
      · rw [hZX]; exact hx
      · have h : x ∈ X ∩ Z := by rw [hZX]; simp
        exact h.2
    have hpx : p ≠ x := by
      obtain ⟨Z, hZβ, hpZ⟩ := hpβ
      intro hpx
      apply hpZ
      rw [hpx]
      exact hxmem Z hZβ
    have hXint : X ∩ ptPerp Γ c {x} = {x} :=
      inter_ptPerp_eq_singleton_of_isNonabsPlane hP hT hX hx
    have hx0 : c x = 0 := hX.1.1.1.1 x hx
    have hex : ∃ Z ∈ tangentBundle Γ c X x, p ∈ Z := by
      by_cases hpX : p ∈ X
      · exact ⟨X, by change IsStarPlane Γ c X ∧ (X = X ∨ X ∩ X = {x}); exact ⟨hX.1, Or.inl rfl⟩,
          hpX⟩
      · rcases dist_eq_two_or_four_of_color_zero hP hp hx0 hpx with h2 | h4
        · refine ⟨ptPerp Γ c {x}, ?_, ?_⟩
          · change IsStarPlane Γ c (ptPerp Γ c {x}) ∧
              (ptPerp Γ c {x} = X ∨ X ∩ ptPerp Γ c {x} = {x})
            exact ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hx0, Or.inr hXint⟩
          · rw [mem_ptPerp]
            exact ⟨hp, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; omega⟩
        · have h4' : Γ.dist x p = 4 := by rw [SimpleGraph.dist_comm]; exact h4
          have hℓhyp : IsHypLine Γ c (starLine Γ c x p) := ⟨x, p, hx0, h4', rfl⟩
          have hxℓ : x ∈ starLine Γ c x p := mem_starLine_left hx0
          have hℓX : ¬ starLine Γ c x p ⊆ X := by
            intro hsub
            exact hpX (hsub (mem_starLine_right hp))
          obtain ⟨Z, ⟨hZplane, hℓZ, hZXint⟩, -⟩ :=
            existsUnique_tangent hP hT c hdeg hreg hii hX hx hℓhyp hxℓ hℓX
          exact ⟨Z, by
            change IsStarPlane Γ c Z ∧ (Z = X ∨ X ∩ Z = {x})
            exact ⟨hZplane, Or.inr hZXint⟩, hℓZ (mem_starLine_right hp)⟩
    obtain ⟨Z, hZβ, hpZ⟩ := hex
    refine ⟨Z, ⟨hZβ, hpZ⟩, ?_⟩
    rintro W ⟨hWβ, hpW⟩
    by_contra hWZ
    have hinter := inter_eq_of_mem_tangentBundle hP hT c hdeg hreg hii hX hx hWβ hZβ hWZ
    have hpint : p ∈ W ∩ Z := ⟨hpW, hpZ⟩
    rw [hinter] at hpint
    exact hpx (by simpa using hpint)

end BundlePoint

section BundlePair

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem existsUnique_isPlaneBundle_of_isNonabs (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCondPrime Γ c)
    {X Y : Set V} {x : V} (hXn : IsNonabsPlane Γ c X) (hY : IsStarPlane Γ c Y)
    (hx : X ∩ Y = {x}) (hXY : X ≠ Y) :
    ∃! β, IsPlaneBundle Γ c β ∧ X ∈ β ∧ Y ∈ β := by
  classical
  have hxX : x ∈ X := by
    have h : x ∈ X ∩ Y := by rw [hx]; simp
    exact h.1
  have hxY : x ∈ Y := by
    have h : x ∈ X ∩ Y := by rw [hx]; simp
    exact h.2
  have hYX : Y ∩ X = {x} := by rw [Set.inter_comm]; exact hx
  refine ⟨tangentBundle Γ c X x, ⟨Or.inr ⟨X, x, hXn, hxX, rfl⟩, ?_, ?_⟩, ?_⟩
  · change IsStarPlane Γ c X ∧ (X = X ∨ X ∩ X = {x})
    exact ⟨hXn.1, Or.inl rfl⟩
  · change IsStarPlane Γ c Y ∧ (Y = X ∨ X ∩ Y = {x})
    exact ⟨hY, Or.inr hx⟩
  · rintro β ⟨hβ, hXβ, hYβ⟩
    rcases hβ with ⟨L, hL, rfl⟩ | ⟨Z, z, hZn, hz, rfl⟩
    ·
      have hLsub : L ⊆ ({x} : Set V) := by
        intro w hw
        have hwX : w ∈ X := hXβ.2 hw
        have hwY : w ∈ Y := hYβ.2 hw
        have hmem : w ∈ X ∩ Y := ⟨hwX, hwY⟩
        rwa [hx] at hmem
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hL
      have ha' : a ∈ ({x} : Set V) := hLsub (mem_starLine_left ha)
      have hb' : b ∈ ({x} : Set V) := hLsub (mem_starLine_right hb)
      exact absurd (by simpa using ha'.trans hb'.symm) hab
    ·
      rcases hXβ.2 with hXZ | hXZint
      · rcases hYβ.2 with hYZ | hYZint
        · exact absurd (hXZ.trans hYZ.symm) hXY
        · have hset : ({z} : Set V) = {x} := by
            rw [← hYZint, ← hXZ, hx]
          have hzx : z = x := by simpa using hset
          rw [← hXZ, hzx]
      · rcases hYβ.2 with hYZ | hYZint
        · have hset : ({z} : Set V) = {x} := by
            rw [← hXZint, ← hYZ, Set.inter_comm, hx]
          have hzx : z = x := by simpa using hset
          have hYn : IsNonabsPlane Γ c Y := hYZ ▸ hZn
          rw [← hYZ, hzx]
          exact (tangentBundle_eq hP hT c hdeg hreg hii hYn hxY
            (by
              change IsStarPlane Γ c X ∧ (X = Y ∨ Y ∩ X = {x})
              exact ⟨hXn.1, Or.inr hYX⟩) hXn).symm
        · have hzx : z = x := by
            have hXYz : X ∩ Y = {z} :=
              inter_eq_of_mem_tangentBundle hP hT c hdeg hreg hii hZn hz hXβ hYβ hXY
            have hset : ({x} : Set V) = {z} := by rw [← hx, ← hXYz]
            have hxz : x = z := by simpa using hset
            exact hxz.symm
          rw [hzx]
          exact (tangentBundle_eq hP hT c hdeg hreg hii hZn (hzx ▸ hz)
            (by
              change IsStarPlane Γ c X ∧ (X = Z ∨ Z ∩ X = {x})
              exact ⟨hXn.1, Or.inr (by rw [hXZint, hzx])⟩) hXn).symm

theorem existsUnique_isPlaneBundle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCondPrime Γ c)
    {X Y : Set V} (hX : IsStarPlane Γ c X) (hY : IsStarPlane Γ c Y) (hXY : X ≠ Y) :
    ∃! β, IsPlaneBundle Γ c β ∧ X ∈ β ∧ Y ∈ β := by
  classical
  have hinter := inter_nonempty hP hT c hdeg hreg hst hii hX hY
  rcases inter_cases hP hT c hdeg hreg hX hY hXY with hemp | ⟨x, hx⟩ | hline
  · rw [hemp] at hinter
    exact absurd hinter (by simp)
  · rcases isStarPlane_cases hP hT c hdeg hreg hX with hXa | hXn
    · rcases isStarPlane_cases hP hT c hdeg hreg hY with hYa | hYn
      · exact (not_inter_eq_singleton_of_isAbsPlane hP hT c hdeg hXa hYa hXY hx).elim
      · have hXY' : Y ∩ X = {x} := by rw [Set.inter_comm]; exact hx
        obtain ⟨β, ⟨hβ, hYβ, hXβ⟩, huniq⟩ :=
          existsUnique_isPlaneBundle_of_isNonabs hP hT c hdeg hreg hii hYn hX hXY' (Ne.symm hXY)
        exact ⟨β, ⟨hβ, hXβ, hYβ⟩, fun β' ⟨hβ', hXβ', hYβ'⟩ => huniq β' ⟨hβ', hYβ', hXβ'⟩⟩
    · exact existsUnique_isPlaneBundle_of_isNonabs hP hT c hdeg hreg hii hXn hY hx hXY
  · refine ⟨axisBundle Γ c (X ∩ Y), ⟨Or.inl ⟨X ∩ Y, hline, rfl⟩, ?_, ?_⟩, ?_⟩
    · change IsStarPlane Γ c X ∧ X ∩ Y ⊆ X
      exact ⟨hX, Set.inter_subset_left⟩
    · change IsStarPlane Γ c Y ∧ X ∩ Y ⊆ Y
      exact ⟨hY, Set.inter_subset_right⟩
    · rintro β ⟨hβ, hXβ, hYβ⟩
      rcases hβ with ⟨L, hL, rfl⟩ | ⟨Z, z, hZn, hz, rfl⟩
      · have hLsub : L ⊆ X ∩ Y := fun w hw => ⟨hXβ.2 hw, hYβ.2 hw⟩
        have hLeq : L = X ∩ Y := by
          obtain ⟨a, b, ha, hb, hab, hLa⟩ := hL
          have haI : a ∈ X ∩ Y := hLsub (by rw [hLa]; exact mem_starLine_left ha)
          have hbI : b ∈ X ∩ Y := hLsub (by rw [hLa]; exact mem_starLine_right hb)
          rw [hLa]
          exact (starLine_eq_of_isStarLine_of_mem hP hT hline haI hbI hab).symm
        rw [hLeq]
      · have hsing : ¬ IsStarLine Γ c ({z} : Set V) := by
          rintro ⟨a, b, ha, hb, hab, hEq⟩
          have ha' : a ∈ ({z} : Set V) := by rw [hEq]; exact mem_starLine_left ha
          have hb' : b ∈ ({z} : Set V) := by rw [hEq]; exact mem_starLine_right hb
          exact hab (by simpa using ha'.trans hb'.symm)
        have hXYz : X ∩ Y = {z} := by
          rcases hXβ.2 with hXZ | hXZint
          · rcases hYβ.2 with hYZ | hYZint
            · exact absurd (hXZ.trans hYZ.symm) hXY
            · rw [hXZ]
              exact hYZint
          · rcases hYβ.2 with hYZ | hYZint
            · rw [hYZ, Set.inter_comm]
              exact hXZint
            · exact inter_eq_of_mem_tangentBundle hP hT c hdeg hreg hii hZn hz hXβ hYβ hXY
        exact (hsing (hXYz ▸ hline)).elim

end BundlePair


end CFSG.Geometry.GeneralizedQuadrangles

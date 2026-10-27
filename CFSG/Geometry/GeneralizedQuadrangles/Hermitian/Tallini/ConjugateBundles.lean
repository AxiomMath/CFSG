module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Conjugacy2
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Bundles

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section ConjugateBundles

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem isHypLine_of_isStarLine_subset_of_isNonabsPlane (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {c : Γ.Coloring (Fin 2)} {X L : Set V} (hX : IsNonabsPlane Γ c X)
    (hL : IsStarLine Γ c L) (hLX : L ⊆ X) : IsHypLine Γ c L := by
  obtain ⟨a, b, ha, hb, hab, hLab⟩ := hL
  have haL : a ∈ L := by rw [hLab]; exact mem_starLine_left ha
  have hbL : b ∈ L := by rw [hLab]; exact mem_starLine_right hb
  have h4 : Γ.dist a b = 4 :=
    dist_eq_four_of_mem_of_isOvoid hP hT hX.2 (hLX haL) (hLX hbL) hab
  exact ⟨a, b, ha, h4, hLab⟩

theorem eq_of_isStarLine_subset (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {L M : Set V} (hL : IsStarLine Γ c L) (hM : IsStarLine Γ c M)
    (hLM : L ⊆ M) : L = M := by
  obtain ⟨a, b, ha, hb, hab, hLab⟩ := hL
  have haL : a ∈ L := by rw [hLab]; exact mem_starLine_left ha
  have hbL : b ∈ L := by rw [hLab]; exact mem_starLine_right hb
  calc L = starLine Γ c a b := hLab
    _ = M := (starLine_eq_of_isStarLine_of_mem hP hT hM (hLM haL) (hLM hbL) hab).symm

private theorem false_of_isConjPlane_inter (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {X' Y Z ℓ : Set V} {x : V} (hX' : IsNonabsPlane Γ c X') (hY : IsNonabsPlane Γ c Y)
    (hZ : IsStarPlane Γ c Z) (hx' : x ∈ X') (hxY : x ∈ Y) (hxZ : x ∈ Z)
    (hconjY : IsConjPlane Γ c X' Y) (hconjZ : IsConjPlane Γ c X' Z)
    (hℓ : IsStarLine Γ c ℓ) (hxℓ : x ∈ ℓ) (hℓY : ℓ ⊆ Y) (hℓX' : ℓ ⊆ X')
    (hℓZ : ¬ ℓ ⊆ Z) (hnotsing : Y ∩ Z ≠ {x}) : False := by
  classical
  have hYZ : Y ≠ Z := fun h => hℓZ (h ▸ hℓY)
  have hii' : TalliniCondPrime Γ c := talliniCondPrime_of_talliniCond hP hT c hdeg hreg hii
  have hne : (Y ∩ Z).Nonempty := inter_nonempty hP hT c hdeg hreg hst hii' hY.1 hZ
  have hline : IsStarLine Γ c (Y ∩ Z) := by
    rcases inter_cases hP hT c hdeg hreg hY.1 hZ hYZ with hemp | hsingle | hline
    · rw [hemp] at hne
      exact absurd hne (by simp)
    · obtain ⟨z, hz⟩ := hsingle
      have hxz : Y ∩ Z = {x} := by
        rw [hz]
        have hmem : x ∈ ({z} : Set V) := by rw [← hz]; exact ⟨hxY, hxZ⟩
        have hxz' : x = z := by simpa using hmem
        rw [hxz']
      exact absurd hxz hnotsing
    · exact hline
  have hxm : x ∈ Y ∩ Z := ⟨hxY, hxZ⟩
  have hIVhyp : IsHypLine Γ c (X' ∩ Y) :=
    isHypLine_inter_of_isConjPlane hP hT c hdeg hreg hst hii hX' hY hconjY
  have hIVstar : IsStarLine Γ c (X' ∩ Y) := IsHypLine.isStarLine hP hIVhyp
  have hIV : X' ∩ Y = ℓ := by
    obtain ⟨a, b, ha, hb, hab, hℓab⟩ := hℓ
    have haℓ : a ∈ ℓ := by rw [hℓab]; exact mem_starLine_left ha
    have hbℓ : b ∈ ℓ := by rw [hℓab]; exact mem_starLine_right hb
    have haIV : a ∈ X' ∩ Y := ⟨hℓX' haℓ, hℓY haℓ⟩
    have hbIV : b ∈ X' ∩ Y := ⟨hℓX' hbℓ, hℓY hbℓ⟩
    calc X' ∩ Y = starLine Γ c a b :=
          starLine_eq_of_isStarLine_of_mem hP hT hIVstar haIV hbIV hab
      _ = ℓ := hℓab.symm
  by_cases hmX' : Y ∩ Z ⊆ X'
  · have hsub : Y ∩ Z ⊆ ℓ := by
      rw [← hIV]
      exact fun w hw => ⟨hmX' hw, hw.1⟩
    have hEq : Y ∩ Z = ℓ := eq_of_isStarLine_subset hP hT hline hℓ hsub
    exact hℓZ (hEq ▸ Set.inter_subset_right)
  · have hperp : ¬ ptPerp Γ c (Y ∩ Z) ⊆ X' := by
      intro hsub
      have hdisj := disjoint_of_ptPerp_subset hP hT c hdeg hreg hX' hline hsub
      exact (Set.disjoint_left.mp hdisj) hxm hx'
    obtain ⟨W, -, huniq⟩ :=
      existsUnique_conjPlane_superset hP hT c hdeg hreg hii hX'.1 hline hmX' hperp
    have hYeq : Y = W := huniq Y ⟨hY.1, Set.inter_subset_left, hconjY⟩
    have hZeq : Z = W := huniq Z ⟨hZ, Set.inter_subset_right, hconjZ⟩
    exact hYZ (hYeq.trans hZeq.symm)

theorem conjBundle_axisBundle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {L : Set V} (hL : IsStarLine Γ c L) :
    conjBundle Γ c (axisBundle Γ c L) = axisBundle Γ c (ptPerp Γ c L) := by
  classical
  obtain ⟨hLperpStar, hLperp⟩ := ptPerp_ptPerp_starLine hP hT c hdeg hreg hL
  ext Y
  constructor
  · rintro ⟨hYplane, hYall⟩
    refine ⟨hYplane, ?_⟩
    intro u huL
    have hu0 : c u = 0 := (mem_ptPerp.mp huL).1
    have huPlane : IsStarPlane Γ c (ptPerp Γ c {u}) :=
      isStarPlane_ptPerp_singleton hP hT c hdeg hu0
    have hLsub : L ⊆ ptPerp Γ c {u} := by
      intro z hz
      rw [mem_ptPerp]
      refine ⟨color_zero_of_mem_isStarLine hL hz, ?_⟩
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rw [SimpleGraph.dist_comm]
      exact (mem_ptPerp.mp huL).2 z hz
    have hconj : IsConjPlane Γ c Y (ptPerp Γ c {u}) := hYall _ ⟨huPlane, hLsub⟩
    exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hYplane hu0).mp ⟨huPlane, hconj⟩
  · rintro ⟨hYplane, hLY⟩
    refine ⟨hYplane, ?_⟩
    intro X hX
    obtain ⟨hXplane, hLX⟩ := hX
    refine ⟨ptPerp Γ c L, hLperpStar, hLY, ?_⟩
    rw [hLperp]
    exact hLX

theorem eq_or_inter_eq_singleton_of_isConjPlane (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {X' X X'' : Set V} {x : V} (hX' : IsNonabsPlane Γ c X') (hX : IsNonabsPlane Γ c X)
    (hX'' : IsNonabsPlane Γ c X'') (hx' : x ∈ X') (hx : x ∈ X) (hx'' : x ∈ X'')
    (hc : IsConjPlane Γ c X' X) (hc'' : IsConjPlane Γ c X' X'') : X = X'' ∨ X ∩ X'' = {x} := by
  classical
  by_cases hXX : X = X''
  · exact Or.inl hXX
  · right
    have hii' : TalliniCondPrime Γ c := talliniCondPrime_of_talliniCond hP hT c hdeg hreg hii
    have hX0 : c x = 0 := hX.1.1.1.1 x hx
    have hne : (X ∩ X'').Nonempty := inter_nonempty hP hT c hdeg hreg hst hii' hX.1 hX''.1
    rcases inter_cases hP hT c hdeg hreg hX.1 hX''.1 hXX with hemp | hsingle | hline
    · rw [hemp] at hne
      exact absurd hne (by simp)
    · obtain ⟨y, hy⟩ := hsingle
      have hxy : x = y := by
        have hmem : x ∈ ({y} : Set V) := by rw [← hy]; exact ⟨hx, hx''⟩
        simpa using hmem
      rw [hy, hxy]
    · exfalso
      have hℓhyp : IsHypLine Γ c (X ∩ X'') :=
        isHypLine_of_isStarLine_subset_of_isNonabsPlane hP hT hX hline Set.inter_subset_left
      have hstep1 : X ∩ X'' ⊆ X' := by
        by_contra hnot
        obtain ⟨y, hyXX'', hyX'⟩ := Set.not_subset.mp hnot
        obtain ⟨hyX, hyX''⟩ := hyXX''
        have hy0 : c y = 0 := hX.1.1.1.1 y hyX
        have hNhyp : IsHypLine Γ c (conjLine Γ c X' y) :=
          (isHypLine_conjLine hP hT c hdeg hreg hX'.1 hy0 hyX').1
        have hNstar : IsStarLine Γ c (conjLine Γ c X' y) := IsHypLine.isStarLine hP hNhyp
        have hNperp : ptPerp Γ c (conjLine Γ c X' y) ⊆ X' :=
          (isHypLine_conjLine hP hT c hdeg hreg hX'.1 hy0 hyX').2.2
        have hNy : y ∈ conjLine Γ c X' y :=
          (isHypLine_conjLine hP hT c hdeg hreg hX'.1 hy0 hyX').2.1
        have hNX : conjLine Γ c X' y ⊆ X :=
          subset_of_isConjPlane hP hT c hdeg hreg hii hX'.1 hX.1 hc hyX hyX'
        have hNX'' : conjLine Γ c X' y ⊆ X'' :=
          subset_of_isConjPlane hP hT c hdeg hreg hii hX'.1 hX''.1 hc'' hyX'' hyX'
        have hdisj : Disjoint (conjLine Γ c X' y) X' :=
          disjoint_of_ptPerp_subset hP hT c hdeg hreg hX' hNstar hNperp
        have hxN : x ∉ conjLine Γ c X' y :=
          fun h => (Set.disjoint_left.mp hdisj) h hx'
        have hNcard : 1 < (conjLine Γ c X' y).ncard := by
          rw [IsHypLine.ncard hP hT c hdeg hreg hNhyp]
          have ht : 2 ≤ t := two_le_t hP hT c hdeg
          omega
        obtain ⟨y', hy'N, hy'y⟩ := Set.exists_ne_of_one_lt_ncard hNcard y
        have hnc : ¬ IsStarCollinear Γ c x y y' := by
          rintro ⟨S, hS, hxS, hyS, hy'S⟩
          have hSeq : S = conjLine Γ c X' y := by
            refine (starLine_eq_of_isStarLine_of_mem hP hT hS hyS hy'S ?_).trans ?_
            · intro h; exact hy'y h.symm
            · exact (starLine_eq_of_isStarLine_of_mem hP hT hNstar hNy hy'N hy'y.symm).symm
          rw [hSeq] at hxS
          exact hxN hxS
        exact hXX (eq_of_isStarPlane hP hT c hdeg hreg hX.1 hX''.1 ⟨hx, hx''⟩
          ⟨hyX, hyX''⟩ ⟨hNX hy'N, hNX'' hy'N⟩ hnc)
      obtain ⟨z, z', hz0, hz'0, hzz', hℓperpEq⟩ :=
        (ptPerp_ptPerp_starLine hP hT c hdeg hreg hline).1
      have hzperp : z ∈ ptPerp Γ c (X ∩ X'') := by
        rw [hℓperpEq]
        exact mem_starLine_left hz0
      have hxℓ : x ∈ X ∩ X'' := ⟨hx, hx''⟩
      have hzX' : z ∉ X' := by
        intro hzX'
        have hℓcard : 1 < (X ∩ X'').ncard := by
          rw [IsHypLine.ncard hP hT c hdeg hreg hℓhyp]
          have ht : 2 ≤ t := two_le_t hP hT c hdeg
          omega
        obtain ⟨y, hyℓ, hyz⟩ := Set.exists_ne_of_one_lt_ncard hℓcard z
        have hzy : Γ.dist z y ≤ 2 := (mem_ptPerp.mp hzperp).2 y hyℓ
        have hyX' : y ∈ X' := hstep1 hyℓ
        have h4 : Γ.dist z y = 4 :=
          dist_eq_four_of_mem_of_isOvoid hP hT hX'.2 hzX' hyX' hyz.symm
        omega
      have hz0' : c z = 0 := (mem_ptPerp.mp hzperp).1
      have hzInterStar : IsStarLine Γ c (ptPerp Γ c {z} ∩ X') :=
        isStarLine_inter_ptPerp_singleton_of_isStarPlane hP hT c hdeg hreg hX'.1 hz0' hzX'
      have hℓsub : X ∩ X'' ⊆ ptPerp Γ c {z} := by
        intro w hw
        rw [mem_ptPerp]
        refine ⟨color_zero_of_mem_isStarLine hline hw, ?_⟩
        intro v hv
        rw [Set.mem_singleton_iff] at hv
        subst hv
        rw [SimpleGraph.dist_comm]
        exact (mem_ptPerp.mp hzperp).2 w hw
      have hInterEq : ptPerp Γ c {z} ∩ X' = X ∩ X'' := by
        have hsub : X ∩ X'' ⊆ ptPerp Γ c {z} ∩ X' := fun w hw => ⟨hℓsub hw, hstep1 hw⟩
        exact (eq_of_isStarLine_subset hP hT hline hzInterStar hsub).symm
      have hxperp : x ∈ ptPerp Γ c {z} := hℓsub hxℓ
      have hzx : z ≠ x := fun h => hzX' (h ▸ hx')
      have hzperpNe : ptPerp Γ c {z} ≠ ptPerp Γ c {x} := by
        intro h
        exact hzx (ptPerp_singleton_injective hP hT hz0' hX0 h)
      have hsetcard :
          {m : Set V | IsHypLine Γ c m ∧ x ∈ m ∧ m ⊆ ptPerp Γ c {z}}.ncard = s :=
        ncard_hypLines_through_subset hP hT c hdeg hreg
          (isStarPlane_ptPerp_singleton hP hT c hdeg hz0') hxperp hzperpNe
      have hs : 2 ≤ s := two_le_s hP hT c hdeg
      have hset2 : 1 < {m : Set V | IsHypLine Γ c m ∧ x ∈ m ∧ m ⊆ ptPerp Γ c {z}}.ncard := by
        rw [hsetcard]; omega
      obtain ⟨R, hRmem, hRne⟩ := Set.exists_ne_of_one_lt_ncard hset2 (X ∩ X'')
      obtain ⟨hRhyp, hxR, hRsubperp⟩ := hRmem
      have hRstar : IsStarLine Γ c R := IsHypLine.isStarLine hP hRhyp
      have hRnotX' : ¬ R ⊆ X' := by
        intro hRsub
        have hsub : R ⊆ ptPerp Γ c {z} ∩ X' := fun w hw => ⟨hRsubperp hw, hRsub hw⟩
        have hEq : R = X ∩ X'' :=
          (eq_of_isStarLine_subset hP hT hRstar hzInterStar hsub).trans hInterEq
        exact hRne hEq
      have hRperpNot : ¬ ptPerp Γ c R ⊆ X' := by
        intro hsub
        have hdisj := disjoint_of_ptPerp_subset hP hT c hdeg hreg hX' hRstar hsub
        exact (Set.disjoint_left.mp hdisj) hxR hx'
      obtain ⟨Z, ⟨hZplane, hRZ, hZconj⟩, -⟩ :=
        existsUnique_conjPlane_superset hP hT c hdeg hreg hii hX'.1 hRstar hRnotX' hRperpNot
      have hxZ : x ∈ Z := hRZ hxR
      have hZnon : IsNonabsPlane Γ c Z := by
        by_contra hnon
        rcases isStarPlane_cases hP hT c hdeg hreg hZplane with habs | hnonab
        · obtain ⟨w, hw0, hZw⟩ := habs
          have hwX' : w ∈ X' := by
            have hmem : ptPerp Γ c {w} ∈ conjNet Γ c X' := by
              rw [← hZw]
              exact ⟨hZplane, hZconj⟩
            exact (ptPerp_mem_conjNet_iff hP hT c hdeg hreg hX'.1 hw0).mp hmem
          have hwx : w = x := by
            have hxperp' : x ∈ ptPerp Γ c {w} := by rw [← hZw]; exact hxZ
            have hle : Γ.dist w x ≤ 2 := by
              have h := (mem_ptPerp.mp hxperp').2 w (by simp)
              rwa [SimpleGraph.dist_comm] at h
            by_contra hwx
            have h4 : Γ.dist w x = 4 :=
              dist_eq_four_of_mem_of_isOvoid hP hT hX'.2 hwX' hx' hwx
            omega
          exact not_subset_ptPerp_singleton_of_isHypLine hP hT hX0 hRhyp hxR
            (by rw [← hwx, ← hZw]; exact hRZ)
        · exact absurd hnonab hnon
      have hℓZ : ¬ X ∩ X'' ⊆ Z := by
        intro hsub
        have hRcard : 1 < R.ncard := by
          rw [IsHypLine.ncard hP hT c hdeg hreg hRhyp]
          have ht : 2 ≤ t := two_le_t hP hT c hdeg
          omega
        obtain ⟨r, hrR, hrx⟩ := Set.exists_ne_of_one_lt_ncard hRcard x
        have hℓcard : 1 < (X ∩ X'').ncard := by
          rw [IsHypLine.ncard hP hT c hdeg hreg hℓhyp]
          have ht : 2 ≤ t := two_le_t hP hT c hdeg
          omega
        obtain ⟨b, hbℓ, hbx⟩ := Set.exists_ne_of_one_lt_ncard hℓcard x
        have hnc : ¬ IsStarCollinear Γ c x r b := by
          rintro ⟨S, hS, hxS, hrS, hbS⟩
          have hSR : S = R := by
            have h1 : S = starLine Γ c x r :=
              starLine_eq_of_isStarLine_of_mem hP hT hS hxS hrS (Ne.symm hrx)
            have h2 : R = starLine Γ c x r :=
              starLine_eq_of_isStarLine_of_mem hP hT hRstar hxR hrR (Ne.symm hrx)
            rw [h1, ← h2]
          have hbR : b ∈ R := by rw [hSR] at hbS; exact hbS
          have hRb : starLine Γ c x b = R :=
            (starLine_eq_of_isStarLine_of_mem hP hT hRstar hxR hbR (Ne.symm hbx)).symm
          have hℓb : starLine Γ c x b = X ∩ X'' :=
            (starLine_eq_of_isStarLine_of_mem hP hT hline hxℓ hbℓ (Ne.symm hbx)).symm
          exact hRne (hRb.symm.trans hℓb)
        have hEq : Z = ptPerp Γ c {z} :=
          eq_of_isStarPlane hP hT c hdeg hreg hZplane
            (isStarPlane_ptPerp_singleton hP hT c hdeg hz0')
            ⟨hxZ, hxperp⟩ ⟨hRZ hrR, hRsubperp hrR⟩ ⟨hsub hbℓ, hℓsub hbℓ⟩ hnc
        exact not_isNonabsPlane_of_isAbsPlane hP hT c hdeg ⟨z, hz0', hEq⟩ hZnon
      by_cases hXZint : X ∩ Z = {x}
      · by_cases hX''Zint : X'' ∩ Z = {x}
        · have hmemX : X ∈ tangentBundle Γ c Z x :=
            ⟨hX.1, Or.inr (by rw [Set.inter_comm]; exact hXZint)⟩
          have hmemX'' : X'' ∈ tangentBundle Γ c Z x :=
            ⟨hX''.1, Or.inr (by rw [Set.inter_comm]; exact hX''Zint)⟩
          have hinter := inter_eq_of_mem_tangentBundle hP hT c hdeg hreg hii' hZnon hxZ
            hmemX hmemX'' hXX
          have hsing : ¬ IsStarLine Γ c ({x} : Set V) := by
            rintro ⟨a, b, ha, hb, hab, hEq⟩
            have ha' : a ∈ ({x} : Set V) := by rw [hEq]; exact mem_starLine_left ha
            have hb' : b ∈ ({x} : Set V) := by rw [hEq]; exact mem_starLine_right hb
            exact hab (by simpa using ha'.trans hb'.symm)
          exact hsing (hinter ▸ hline)
        · exact false_of_isConjPlane_inter hP hT c hdeg hreg hst hii hX' hX'' hZplane hx'
            hx'' hxZ hc'' hZconj hline ⟨hx, hx''⟩ Set.inter_subset_right hstep1 hℓZ hX''Zint
      · exact false_of_isConjPlane_inter hP hT c hdeg hreg hst hii hX' hX hZplane hx'
          hx hxZ hc hZconj hline ⟨hx, hx''⟩ Set.inter_subset_left hstep1 hℓZ hXZint

end ConjugateBundles

end CFSG.Geometry.GeneralizedQuadrangles

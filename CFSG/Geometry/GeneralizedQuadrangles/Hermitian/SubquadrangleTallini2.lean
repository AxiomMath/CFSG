module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.SubquadranglePlanes
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.TraceCounting
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Conjugacy

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

private theorem color_eq_zero_of_mem_isStarLine {P' : Set V}
    {X : Set (subquadrangleSet Γ c P')}
    (hX : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X) {z : subquadrangleSet Γ c P'} (hz : z ∈ X) :
    subquadrangleColoring c P' z = 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hX
  exact color_eq_zero_of_mem_starLine hz

private theorem ncard_starLine_le (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {X : Set (subquadrangleSet Γ c P')}
    (hX : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X) : X.ncard ≤ q ^ 2 + 1 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hΓ.thick c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hΓ.thick c hΓ.deg hF hΓ.two_le
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hX
  rcases dist_eq_two_or_four_of_color_zero hP' ha hb hab with h2 | h4
  · rw [starLine_eq_neighborSet hP' hT' (subquadrangleColoring c P') ha h2, ncard_neighborSet]
    have hL1 : subquadrangleColoring c P' (commonNeighbor hP' h2) = 1 :=
      color_eq_one_of_adj_of_color_eq_zero ha (commonNeighbor_adj_left hP' h2)
    rw [degree_subquadrangleGraph hΓ hF, if_neg (by rw [hL1]; decide)]
  · have ha0 : c a.1 = 0 := by rwa [subquadrangleColoring_apply] at ha
    have haP : a.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero ha
    have h4amb : Γ.dist a.1 b.1 = 4 := by
      have h := h4
      rwa [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF a.2 b.2]
        at h
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective,
      starLine_subquadrangle_of_dist_four hΓ hF ha h4amb,
      hΓ.span a.1 b.1 (hF.1 a.1 haP) h4amb]
    have hq := hΓ.two_le
    nlinarith

private theorem one_lt_ncard_of_isStarLine {P' : Set V}
    {X : Set (subquadrangleSet Γ c P')}
    (hX : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X) : 1 < X.ncard := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hX
  exact (Set.one_lt_ncard (s := starLine (Γ.induce (subquadrangleSet Γ c P'))
    (subquadrangleColoring c P') a b)).mpr
    ⟨a, mem_starLine_left ha, b, mem_starLine_right hb, hab⟩

private theorem exists_point_not_mem_starLine (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {X : Set (subquadrangleSet Γ c P')}
    (hX : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X) :
    ∃ w : subquadrangleSet Γ c P', subquadrangleColoring c P' w = 0 ∧ w ∉ X := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hXle : X.ncard ≤ q ^ 2 + 1 := ncard_starLine_le hΓ hF hX
  have hpts : {w : subquadrangleSet Γ c P' | subquadrangleColoring c P' w = 0}.ncard =
      (q ^ 2 + 1) * (q ^ 2 * q + 1) := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
    have hval : Subtype.val '' {w : subquadrangleSet Γ c P' |
        subquadrangleColoring c P' w = 0} = P' := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact mem_P'_of_subquadrangleColoring_eq_zero hw
      · intro hx
        refine ⟨⟨x, mem_subquadrangleSet.mpr (Or.inl hx)⟩, ?_, rfl⟩
        simpa [subquadrangleColoring_apply] using hF.1 x hx
    rw [hval, ncard_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF]
  have hlt : X.ncard < {w : subquadrangleSet Γ c P' |
      subquadrangleColoring c P' w = 0}.ncard := by
    rw [hpts]
    have hq : 2 ≤ q := hΓ.two_le
    have hq3 : 0 < q ^ 3 := by positivity
    calc X.ncard ≤ q ^ 2 + 1 := hXle
      _ = (q ^ 2 + 1) * 1 := (Nat.mul_one _).symm
      _ < (q ^ 2 + 1) * (q ^ 3 + 1) :=
          Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
  exact Set.exists_mem_notMem_of_ncard_lt_ncard hlt

private theorem exists_isProperVariety_of_common_mem_ne (hΓ : IsThasQuadrangle Γ c q)
    {P' : Set V} (hF : IsFullSubquadrangle c P' q) {M M' : Set (subquadrangleSet Γ c P')}
    (hM : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') M)
    (hM' : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') M')
    {z : subquadrangleSet Γ c P'} (hzM : z ∈ M) (hzM' : z ∈ M') (hne : M ≠ M') :
    ∃ X, IsProperVariety (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X ∧ M ∪ M' ⊆ X := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hΓ.thick c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hΓ.thick c hΓ.deg hF hΓ.two_le
  have hii := talliniCondPrime_subquadrangle hΓ hF
  have hz0 : subquadrangleColoring c P' z = 0 :=
    color_eq_zero_of_mem_isStarLine hM hzM
  obtain ⟨x, hxM, hxz⟩ :=
    Set.exists_ne_of_one_lt_ncard (one_lt_ncard_of_isStarLine hM) z
  obtain ⟨y, hyM', hyz⟩ :=
    Set.exists_ne_of_one_lt_ncard (one_lt_ncard_of_isStarLine hM') z
  have hx0 : subquadrangleColoring c P' x = 0 :=
    color_eq_zero_of_mem_isStarLine hM hxM
  have hy0 : subquadrangleColoring c P' y = 0 :=
    color_eq_zero_of_mem_isStarLine hM' hyM'
  have hMx : M = starLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') z x :=
    starLine_eq_of_isStarLine_of_mem hP' hT' hM hzM hxM hxz.symm
  have hM'y : M' = starLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') z y :=
    starLine_eq_of_isStarLine_of_mem hP' hT' hM' hzM' hyM' hyz.symm
  have hxy : x ≠ y := by
    intro hxy
    exact hne (by rw [hMx, hM'y, hxy])
  have hnc : ¬ IsStarCollinear (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') z x y := by
    rintro ⟨N, hN, hzN, hxN, hyN⟩
    have hNz : N = starLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') z x :=
      starLine_eq_of_isStarLine_of_mem hP' hT' hN hzN hxN hxz.symm
    have hyM : y ∈ M := by rw [hMx, ← hNz]; exact hyN
    exact hne (by
      rw [hM'y]
      exact starLine_eq_of_isStarLine_of_mem hP' hT' hM hzM hyM hyz.symm)
  obtain ⟨X, hX, hzX, hxX, hyX⟩ := hii z x y hz0 hx0 hy0 hnc
  refine ⟨X, hX.1, ?_⟩
  have hMX : M ⊆ X := by
    rw [hMx]
    exact hX.1.1.2 z hzX x hxX hxz.symm
  have hM'X : M' ⊆ X := by
    rw [hM'y]
    exact hX.1.1.2 z hzX y hyX hyz.symm
  intro a ha
  rcases ha with ha | ha
  · exact hMX ha
  · exact hM'X ha

private theorem exists_isProperVariety_of_common_mem (hΓ : IsThasQuadrangle Γ c q)
    {P' : Set V} (hF : IsFullSubquadrangle c P' q) {M M' : Set (subquadrangleSet Γ c P')}
    (hM : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') M)
    (hM' : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') M')
    {z : subquadrangleSet Γ c P'} (hzM : z ∈ M) (hzM' : z ∈ M') :
    ∃ X, IsProperVariety (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X ∧ M ∪ M' ⊆ X := by
  classical
  by_cases hEq : M = M'
  · obtain ⟨w, hw0, hwM⟩ := exists_point_not_mem_starLine hΓ hF hM
    have hz0 : subquadrangleColoring c P' z = 0 :=
      color_eq_zero_of_mem_isStarLine hM hzM
    have hzw : z ≠ w := fun h => hwM (h ▸ hzM)
    have hM'' : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') (starLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') z w) :=
      isStarLine_starLine hz0 hw0 hzw
    have hne : M ≠ starLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') z w := by
      intro h
      exact hwM (by rw [h]; exact mem_starLine_right hw0)
    obtain ⟨X, hX, hsub⟩ :=
      exists_isProperVariety_of_common_mem_ne hΓ hF hM hM'' hzM
        (mem_starLine_left hz0) hne
    refine ⟨X, hX, ?_⟩
    have hM'M : M' = M := hEq.symm
    rw [hM'M]
    intro a ha
    rcases ha with ha | ha
    · exact hsub (Or.inl ha)
    · exact hsub (Or.inl ha)
  · exact exists_isProperVariety_of_common_mem_ne hΓ hF hM hM' hzM hzM' hEq

private theorem isStarPlane_of_isProperVariety (hΓ : IsThasQuadrangle Γ c q)
    {P' : Set V} (hF : IsFullSubquadrangle c P' q) {X : Set (subquadrangleSet Γ c P')}
    (hX : IsProperVariety (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X)
    {L L' : Set (subquadrangleSet Γ c P')}
    (hL : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') L)
    (hL' : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') L')
    (hLX : L ⊆ X) (hL'X : L' ⊆ X) (hne : L ≠ L') :
    IsStarPlane (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hΓ.thick c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hΓ.thick c hΓ.deg hF hΓ.two_le
  obtain ⟨a, haL, b, hbL, hab⟩ :=
    (Set.one_lt_ncard (s := L)).mp (one_lt_ncard_of_isStarLine hL)
  have hLnotsub : ¬ L' ⊆ L := by
    intro hsub
    obtain ⟨a', ha'L', b', hb'L', ha'b'⟩ :=
      (Set.one_lt_ncard (s := L')).mp (one_lt_ncard_of_isStarLine hL')
    have hL'eq : L' = starLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') a' b' :=
      starLine_eq_of_isStarLine_of_mem hP' hT' hL' ha'L' hb'L' ha'b'
    have ha'L : a' ∈ L := hsub ha'L'
    have hb'L : b' ∈ L := hsub hb'L'
    exact hne (by
      rw [hL'eq]
      exact starLine_eq_of_isStarLine_of_mem hP' hT' hL ha'L hb'L ha'b')
  obtain ⟨c0, hc0L', hc0L⟩ : ∃ c0, c0 ∈ L' ∧ c0 ∉ L := by
    by_contra h
    push Not at h
    exact hLnotsub h
  refine ⟨hX, a, hLX haL, b, hLX hbL, c0, hL'X hc0L', ?_⟩
  intro hcol
  obtain ⟨N, hN, haN, hbN, hcN⟩ := hcol
  have hNL : N = starLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') a b :=
    starLine_eq_of_isStarLine_of_mem hP' hT' hN haN hbN hab
  have hcL : c0 ∈ L := by
    rw [starLine_eq_of_isStarLine_of_mem hP' hT' hL haL hbL hab]
    rwa [hNL] at hcN
  exact hc0L hcL

private theorem exists_isProperVariety_of_disjoint (hΓ : IsThasQuadrangle Γ c q)
    {P' : Set V} (hF : IsFullSubquadrangle c P' q)
    {L L' : Set (subquadrangleSet Γ c P')}
    (hL : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') L)
    (hL' : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') L')
    (hdisj : Disjoint L L') {T : Set (subquadrangleSet Γ c P')}
    (hT : IsNonabsPlane (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') T)
    (hLT : L ⊆ T) (hL'T : L' ⊆ T) :
    ∃ X, IsProperVariety (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X ∧
      ptPerp (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') L ∪
        ptPerp (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') L' ⊆ X := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hΓ.thick c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hΓ.thick c hΓ.deg hF hΓ.two_le
  have hdeg' : ∀ w : subquadrangleSet Γ c P',
      (Γ.induce (subquadrangleSet Γ c P')).degree w =
        if subquadrangleColoring c P' w = 0 then q + 1 else q ^ 2 + 1 :=
    fun w => degree_subquadrangleGraph hΓ hF w
  have hreg' : ∀ w : subquadrangleSet Γ c P', subquadrangleColoring c P' w = 0 →
      IsRegularVertex (Γ.induce (subquadrangleSet Γ c P')) w :=
    fun w hw => isRegularVertex_subquadrangle hΓ hF w hw
  obtain ⟨u, v, hu0, huv, hTP, hval⟩ :=
    (isNonabsPlane_subquadrangle_iff hΓ hF).mp hT
  have hTovoid : IsOvoid (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') T := hT.2
  have huv_ne : u ≠ v := by
    intro h; rw [h] at huv; simp at huv
  have hLstar : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') L := hL
  have hL'star : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') L' := hL'
  obtain ⟨a, b, ha, hb, hab, hLeq⟩ := hL
  obtain ⟨a', b', ha', hb', ha'b', hL'eq⟩ := hL'
  have haL : a ∈ L := by rw [hLeq]; exact mem_starLine_left ha
  have hbL : b ∈ L := by rw [hLeq]; exact mem_starLine_right hb
  have ha'L' : a' ∈ L' := by rw [hL'eq]; exact mem_starLine_left ha'
  have hb'L' : b' ∈ L' := by rw [hL'eq]; exact mem_starLine_right hb'
  have haT : a ∈ T := hLT haL
  have hbT : b ∈ T := hLT hbL
  have ha'T : a' ∈ T := hL'T ha'L'
  have hb'T : b' ∈ T := hL'T hb'L'
  have hv0 : c v = 0 := by
    have h := (hP.eq_iff_even_dist c v u).2 (by
      rw [SimpleGraph.dist_comm, huv]; exact ⟨2, rfl⟩)
    rwa [h, hu0]
  have ha0 : c a.1 = 0 := by rwa [subquadrangleColoring_apply] at ha
  have hb0 : c b.1 = 0 := by rwa [subquadrangleColoring_apply] at hb
  have ha'0 : c a'.1 = 0 := by rwa [subquadrangleColoring_apply] at ha'
  have hb'0 : c b'.1 = 0 := by rwa [subquadrangleColoring_apply] at hb'
  have haP : a.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero ha
  have hbP : b.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hb
  have ha'P : a'.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero ha'
  have hb'P : b'.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hb'
  have ha_trace : a.1 ∈ traceSet Γ u v := by
    have : a.1 ∈ Subtype.val '' T := ⟨a, haT, rfl⟩
    rwa [hval] at this
  have hb_trace : b.1 ∈ traceSet Γ u v := by
    have : b.1 ∈ Subtype.val '' T := ⟨b, hbT, rfl⟩
    rwa [hval] at this
  have ha'_trace : a'.1 ∈ traceSet Γ u v := by
    have : a'.1 ∈ Subtype.val '' T := ⟨a', ha'T, rfl⟩
    rwa [hval] at this
  have hb'_trace : b'.1 ∈ traceSet Γ u v := by
    have : b'.1 ∈ Subtype.val '' T := ⟨b', hb'T, rfl⟩
    rwa [hval] at this
  have hab4' : (Γ.induce (subquadrangleSet Γ c P')).dist a b = 4 := by
    rcases dist_eq_two_or_four_of_color_zero hP' ha hb hab with h2 | h4
    · exfalso
      exact absurd (dist_eq_four_of_mem_of_isOvoid hP' hT' hTovoid haT hbT hab) (by omega)
    · exact h4
  have hab4 : Γ.dist a.1 b.1 = 4 := by
    have h := hab4'
    rwa [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF a.2 b.2]
      at h
  have ha'b'4' : (Γ.induce (subquadrangleSet Γ c P')).dist a' b' = 4 := by
    rcases dist_eq_two_or_four_of_color_zero hP' ha' hb' ha'b' with h2 | h4
    · exfalso
      exact absurd (dist_eq_four_of_mem_of_isOvoid hP' hT' hTovoid ha'T hb'T ha'b') (by omega)
    · exact h4
  have ha'b'4 : Γ.dist a'.1 b'.1 = 4 := by
    have h := ha'b'4'
    rwa [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF a'.2 b'.2]
      at h
  have hLspan : Subtype.val '' L = spanSet Γ a.1 b.1 := by
    rw [hLeq]
    exact starLine_subquadrangle_of_dist_four hΓ hF ha hab4
  have hL'span : Subtype.val '' L' = spanSet Γ a'.1 b'.1 := by
    rw [hL'eq]
    exact starLine_subquadrangle_of_dist_four hΓ hF ha' ha'b'4
  have hspan_disj : ∀ w, w ∈ spanSet Γ u v → w ∉ P' := by
    intro w hwspan hwP
    have hw0 : c w = 0 := (color_eq_of_mem_span hP hΓ.thick c huv hwspan).trans hu0
    let w' : subquadrangleSet Γ c P' := ⟨w, mem_subquadrangleSet.mpr (Or.inl hwP)⟩
    have hw'0 : subquadrangleColoring c P' w' = 0 := by
      rw [subquadrangleColoring_apply]; exact hw0
    have hdist : ∀ t ∈ T, (Γ.induce (subquadrangleSet Γ c P')).dist w' t = 2 := by
      intro t ht
      rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF w'.2 t.2]
      have ht' : t.1 ∈ traceSet Γ u v := by
        have hmem : t.1 ∈ Subtype.val '' T := ⟨t, ht, rfl⟩
        rwa [hval] at hmem
      exact dist_eq_two_of_mem_span_of_mem_trace hP hΓ.thick huv hwspan ht'
    let f : subquadrangleSet Γ c P' → subquadrangleSet Γ c P' := fun t =>
      if h : t ∈ T then commonNeighbor hP' (hdist t h) else w'
    have hfmem : ∀ t ∈ T, f t ∈
        (Γ.induce (subquadrangleSet Γ c P')).neighborSet w' := by
      intro t ht
      rw [mem_neighborSet]
      simp only [f, dif_pos ht]
      exact commonNeighbor_adj_left hP' (hdist t ht)
    have hfinj : Set.InjOn f T := by
      intro t ht t' ht' heq
      have htL : (Γ.induce (subquadrangleSet Γ c P')).Adj (f t) t := by
        simp only [f, dif_pos ht]
        exact (commonNeighbor_adj_right hP' (hdist t ht)).symm
      have ht'L : (Γ.induce (subquadrangleSet Γ c P')).Adj (f t) t' := by
        rw [heq]
        simp only [f, dif_pos ht']
        exact (commonNeighbor_adj_right hP' (hdist t' ht')).symm
      by_contra hne
      have h4 := dist_eq_four_of_mem_of_isOvoid hP' hT' hTovoid ht ht' hne
      have h2 := dist_eq_two_of_adj_of_adj_of_ne hP' htL.symm ht'L hne
      omega
    have hcard : T.ncard ≤ q + 1 := by
      rw [← hfinj.ncard_image]
      calc (f '' T).ncard ≤
            ((Γ.induce (subquadrangleSet Γ c P')).neighborSet w').ncard :=
            Set.ncard_le_ncard (by rintro _ ⟨t, ht, rfl⟩; exact hfmem t ht)
        _ = (Γ.induce (subquadrangleSet Γ c P')).degree w' := ncard_neighborSet _ _
        _ = q + 1 := by rw [degree_subquadrangleGraph hΓ hF w', if_pos hw'0]
    have hTcard : T.ncard = q ^ 3 + 1 := by
      rw [ncard_of_isOvoid hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q)
        hdeg' hTovoid]
      ring
    have hq : 2 ≤ q := hΓ.two_le
    have hq3 : q < q ^ 3 := by
      have hqpos : 0 < q := by omega
      calc q = q * 1 := (Nat.mul_one _).symm
        _ < q * q := Nat.mul_lt_mul_of_pos_left (by omega) hqpos
        _ ≤ q * q * q := by
            have hle := Nat.mul_le_mul_left (q * q) (by omega : 1 ≤ q)
            simpa using hle
        _ = q ^ 3 := by ring
    omega
  have huP' : u ∉ P' := hspan_disj u (left_mem_spanSet huv)
  have hvP' : v ∉ P' := hspan_disj v (right_mem_spanSet huv)
  have hspan_trace : spanSet Γ u v ⊆ traceSet Γ a.1 b.1 := by
    intro w hw
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_mem_span_of_mem_trace hP hΓ.thick huv hw ha_trace
    · rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_mem_span_of_mem_trace hP hΓ.thick huv hw hb_trace
  have hspan_trace' : spanSet Γ u v ⊆ traceSet Γ a'.1 b'.1 := by
    intro w hw
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_mem_span_of_mem_trace hP hΓ.thick huv hw ha'_trace
    · rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_mem_span_of_mem_trace hP hΓ.thick huv hw hb'_trace
  have htrace_inter : traceSet Γ a.1 b.1 ∩ traceSet Γ a'.1 b'.1 = spanSet Γ u v := by
    refine Set.Subset.antisymm ?_ (fun w hw => ⟨hspan_trace hw, hspan_trace' hw⟩)
    intro z hz
    obtain ⟨hza, hza'⟩ := hz
    have haa'4 : Γ.dist a.1 a'.1 = 4 := by
      have hne : a.1 ≠ a'.1 := by
        intro h
        exact Set.disjoint_left.mp hdisj haL (by
          have : a = a' := Subtype.ext h
          rw [this]; exact ha'L')
      exact dist_eq_four_of_mem_trace hP huv ha_trace ha'_trace hne
    have hba'4 : Γ.dist b.1 a'.1 = 4 := by
      have hne : b.1 ≠ a'.1 := by
        intro h
        exact Set.disjoint_left.mp hdisj hbL (by
          have : b = a' := Subtype.ext h
          rw [this]; exact ha'L')
      exact dist_eq_four_of_mem_trace hP huv hb_trace ha'_trace hne
    have hcl : a'.1 ∉ clSet Γ a.1 b.1 := by
      intro hcl
      obtain ⟨w, hwspan, hle⟩ := hcl
      have hwL : w ∈ Subtype.val '' L := by rwa [hLspan]
      obtain ⟨t, htL, htw⟩ := hwL
      have htT : t ∈ T := hLT htL
      have hta' : t ≠ a' := by
        intro h
        exact Set.disjoint_left.mp hdisj htL (h ▸ ha'L')
      have hle' : Γ.dist a'.1 t.1 ≤ 2 := by rw [htw]; exact hle
      have ht0 : c t.1 = 0 := by
        have := color_eq_zero_of_mem_isStarLine hLstar htL
        rwa [subquadrangleColoring_apply] at this
      have hne0 : Γ.dist a'.1 t.1 ≠ 0 := by
        intro h0
        have hta'_eq : a' = t := Subtype.ext ((hP.connected.dist_eq_zero_iff).mp h0)
        exact hta' hta'_eq.symm
      have heven : Even (Γ.dist a'.1 t.1) :=
        (hP.eq_iff_even_dist c a'.1 t.1).1 (by rw [ha'0, ht0])
      have h4 : Γ.dist a'.1 t.1 = 4 := by
        have h := dist_eq_four_of_mem_of_isOvoid hP' hT' hTovoid ha'T htT (by
          intro h; exact hta' h.symm)
        rwa [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF
          a'.2 t.2] at h
      obtain ⟨k, hk⟩ := heven
      omega
    have hu_centre : u ∈ centreSet Γ a.1 b.1 a'.1 := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [SimpleGraph.dist_comm] using ha_trace.1
      · simpa [SimpleGraph.dist_comm] using hb_trace.1
      · simpa [SimpleGraph.dist_comm] using ha'_trace.1
    have hv_centre : v ∈ centreSet Γ a.1 b.1 a'.1 := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [SimpleGraph.dist_comm] using ha_trace.2
      · simpa [SimpleGraph.dist_comm] using hb_trace.2
      · simpa [SimpleGraph.dist_comm] using ha'_trace.2
    have huv_ne : u ≠ v := by
      intro h; rw [h] at huv; simp at huv
    have hcent := centreSet_eq_spanSet hΓ ha0 hab4 haa'4 hba'4 hcl hu_centre hv_centre huv_ne
    have hz_centre : z ∈ centreSet Γ a.1 b.1 a'.1 := ⟨hza, hza'.1⟩
    rwa [hcent] at hz_centre
  have hd_trace : ∀ d : subquadrangleSet Γ c P', d ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') L → d.1 ∈ traceSet Γ a.1 b.1 := by
    intro d hd
    have hdimg : d.1 ∈ Subtype.val '' ptPerp (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') L := ⟨d, hd, rfl⟩
    rw [ptPerp_subquadrangle hΓ hF, hLspan] at hdimg
    have h := hdimg.1
    rw [← starLine_eq_spanSet hP hΓ.thick c ha0 hab4] at h
    rwa [ptPerp_starLine_eq_traceSet hP hΓ.thick c ha0 hab4] at h
  have hd_P : ∀ d : subquadrangleSet Γ c P', d ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') L → d.1 ∈ P' := by
    intro d hd
    have hdimg : d.1 ∈ Subtype.val '' ptPerp (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') L := ⟨d, hd, rfl⟩
    rw [ptPerp_subquadrangle hΓ hF, hLspan] at hdimg
    exact hdimg.2
  have hd_P' : ∀ d : subquadrangleSet Γ c P',
      d ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') L' → d.1 ∈ P' := by
    intro d hd
    have hdimg : d.1 ∈ Subtype.val '' ptPerp (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') L' := ⟨d, hd, rfl⟩
    rw [ptPerp_subquadrangle hΓ hF, hL'span] at hdimg
    exact hdimg.2
  have hLcard : L.ncard = q + 1 := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, hLspan,
      hΓ.span a.1 b.1 (hF.1 a.1 haP) hab4]
  have hL'card : L'.ncard = q + 1 := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, hL'span,
      hΓ.span a'.1 b'.1 (hF.1 a'.1 ha'P) ha'b'4]
  have hA_eq : ∀ d : subquadrangleSet Γ c P',
      d ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') L →
      {t : subquadrangleSet Γ c P' | t ∈ T ∧
        (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2} = L := by
    intro d hd
    have hdT : d.1 ∈ traceSet Γ a.1 b.1 := hd_trace d hd
    have hd0 : c d.1 = 0 := by rw [← subquadrangleColoring_apply]; exact hd.1
    have hLsub : L ⊆ {t : subquadrangleSet Γ c P' | t ∈ T ∧
        (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2} := by
      intro t htL
      have htT : t ∈ T := hLT htL
      have htspan : t.1 ∈ spanSet Γ a.1 b.1 := by
        have : t.1 ∈ Subtype.val '' L := ⟨t, htL, rfl⟩
        rwa [hLspan] at this
      have hdist : Γ.dist d.1 t.1 = 2 := by
        rw [SimpleGraph.dist_comm]
        exact dist_eq_two_of_mem_span_of_mem_trace hP hΓ.thick hab4 htspan hdT
      refine ⟨htT, ?_⟩
      rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF d.2 t.2]
      exact hdist
    have hAcard : {t : subquadrangleSet Γ c P' | t ∈ T ∧
        (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2}.ncard ≤ q + 1 := by
      let f : subquadrangleSet Γ c P' → subquadrangleSet Γ c P' := fun t =>
        if h : t ∈ T ∧ (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2 then
          commonNeighbor hP' h.2 else d
      have hfmem : ∀ t ∈ {t : subquadrangleSet Γ c P' | t ∈ T ∧
          (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2},
          f t ∈ (Γ.induce (subquadrangleSet Γ c P')).neighborSet d := by
        intro t ht
        have hcond : t ∈ T ∧ (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2 := ht
        rw [mem_neighborSet]
        simp only [f, dif_pos hcond]
        exact commonNeighbor_adj_left hP' hcond.2
      have hfinj : Set.InjOn f {t : subquadrangleSet Γ c P' | t ∈ T ∧
          (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2} := by
        intro t ht t' ht' heq
        have hcond : t ∈ T ∧ (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2 := ht
        have hcond' : t' ∈ T ∧ (Γ.induce (subquadrangleSet Γ c P')).dist d t' = 2 := ht'
        have htL : (Γ.induce (subquadrangleSet Γ c P')).Adj (f t) t := by
          simp only [f, dif_pos hcond]
          exact (commonNeighbor_adj_right hP' hcond.2).symm
        have ht'L : (Γ.induce (subquadrangleSet Γ c P')).Adj (f t) t' := by
          rw [heq]
          simp only [f, dif_pos hcond']
          exact (commonNeighbor_adj_right hP' hcond'.2).symm
        by_contra hne
        have h4 := dist_eq_four_of_mem_of_isOvoid hP' hT' hTovoid ht.1 ht'.1 hne
        have h2 := dist_eq_two_of_adj_of_adj_of_ne hP' htL.symm ht'L hne
        omega
      rw [← hfinj.ncard_image]
      calc (f '' {t : subquadrangleSet Γ c P' | t ∈ T ∧
            (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2}).ncard
          ≤ ((Γ.induce (subquadrangleSet Γ c P')).neighborSet d).ncard :=
            Set.ncard_le_ncard (by rintro _ ⟨t, ht, rfl⟩; exact hfmem t ht)
        _ = (Γ.induce (subquadrangleSet Γ c P')).degree d := ncard_neighborSet _ _
        _ = q + 1 := by rw [degree_subquadrangleGraph hΓ hF d, if_pos hd.1]
    refine (Set.eq_of_subset_of_ncard_le hLsub ?_).symm
    rw [hLcard]
    exact hAcard
  have hdL'_not : ∀ d : subquadrangleSet Γ c P',
      d ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') L →
      ∀ t ∈ L', (Γ.induce (subquadrangleSet Γ c P')).dist d t ≠ 2 := by
    intro d hd t htL' hdt
    have htT : t ∈ T := hL'T htL'
    have hA := hA_eq d hd
    have hmem : t ∈ {t : subquadrangleSet Γ c P' | t ∈ T ∧
        (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2} := ⟨htT, hdt⟩
    rw [hA] at hmem
    exact Set.disjoint_left.mp hdisj hmem htL'
  have hdL'_ne : ∀ d : subquadrangleSet Γ c P',
      d ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') L →
      d ∉ L' := by
    intro d hd hdL'
    have hdT : d ∈ T := hL'T hdL'
    have hA := hA_eq d hd
    have hpos : 0 < L.ncard := by rw [hLcard]; omega
    obtain ⟨t, htL⟩ := (Set.ncard_pos (s := L)).mp hpos
    have ht2 : (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2 := by
      have hmem : t ∈ {t : subquadrangleSet Γ c P' | t ∈ T ∧
          (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2} := by
        rw [hA]; exact htL
      exact hmem.2
    have htd : t ≠ d := by
      intro h
      exact Set.disjoint_left.mp hdisj (h ▸ htL) hdL'
    exact absurd (dist_eq_four_of_mem_of_isOvoid hP' hT' hTovoid hdT (hLT htL)
      (by intro h; exact htd h.symm)) (by omega)
  have hd_not_cl : ∀ d : subquadrangleSet Γ c P',
      d ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') L →
      d.1 ∉ clSet Γ a'.1 b'.1 := by
    intro d hd hcl
    obtain ⟨w, hwspan, hle⟩ := hcl
    have hwL' : w ∈ Subtype.val '' L' := by rwa [hL'span]
    obtain ⟨t, htL', htw⟩ := hwL'
    have hle' : Γ.dist d.1 t.1 ≤ 2 := by rw [htw]; exact hle
    have hd0 : c d.1 = 0 := by rw [← subquadrangleColoring_apply]; exact hd.1
    have ht0 : c t.1 = 0 := by
      have := color_eq_zero_of_mem_isStarLine hL'star htL'
      rwa [subquadrangleColoring_apply] at this
    have hne : d.1 ≠ t.1 := by
      intro h
      exact hdL'_ne d hd (Subtype.ext h ▸ htL')
    have hne0 : Γ.dist d.1 t.1 ≠ 0 := by
      intro h0
      exact hne ((hP.connected.dist_eq_zero_iff).mp h0)
    have heven : Even (Γ.dist d.1 t.1) :=
      (hP.eq_iff_even_dist c d.1 t.1).1 (by rw [hd0, ht0])
    obtain ⟨k, hk⟩ := heven
    have hdt : Γ.dist d.1 t.1 = 2 := by omega
    have hdt' : (Γ.induce (subquadrangleSet Γ c P')).dist d t = 2 := by
      rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF d.2 t.2]
      exact hdt
    exact hdL'_not d hd t htL' hdt'
  have hMstar : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') (ptPerp (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') L) :=
    (ptPerp_ptPerp_starLine hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q)
      hdeg' hreg' hLstar).1
  have hMpos : 0 < (ptPerp (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') L).ncard := by
    have := one_lt_ncard_of_isStarLine hMstar
    omega
  obtain ⟨d, hd⟩ := (Set.ncard_pos (s := ptPerp (Γ.induce (subquadrangleSet Γ c P'))
    (subquadrangleColoring c P') L)).mp hMpos
  have hd_trace' : d.1 ∈ traceSet Γ a.1 b.1 := hd_trace d hd
  have hdP : d.1 ∈ P' := hd_P d hd
  have hd0 : c d.1 = 0 := by rw [← subquadrangleColoring_apply]; exact hd.1
  have hd_cl : d.1 ∉ clSet Γ a'.1 b'.1 := hd_not_cl d hd
  have hd_a'4 : Γ.dist a'.1 d.1 = 4 := by
    have hgt : 2 < Γ.dist d.1 a'.1 := by
      by_contra hle
      exact hd_cl ⟨a'.1, left_mem_spanSet ha'b'4, by omega⟩
    have heven : Even (Γ.dist d.1 a'.1) :=
      (hP.eq_iff_even_dist c d.1 a'.1).1 (by rw [hd0, ha'0])
    have hle4 : Γ.dist d.1 a'.1 ≤ 4 := hP.dist_le (by norm_num) _ _
    rw [SimpleGraph.dist_comm]
    obtain ⟨k, hk⟩ := heven
    omega
  have hd_b'4 : Γ.dist b'.1 d.1 = 4 := by
    have hgt : 2 < Γ.dist d.1 b'.1 := by
      by_contra hle
      exact hd_cl ⟨b'.1, right_mem_spanSet ha'b'4, by omega⟩
    have heven : Even (Γ.dist d.1 b'.1) :=
      (hP.eq_iff_even_dist c d.1 b'.1).1 (by rw [hd0, hb'0])
    have hle4 : Γ.dist d.1 b'.1 ≤ 4 := hP.dist_le (by norm_num) _ _
    rw [SimpleGraph.dist_comm]
    obtain ⟨k, hk⟩ := heven
    omega
  have hcentre_card : (centreSet Γ a'.1 b'.1 d.1).ncard = q + 1 :=
    ncard_centreSet hΓ ha'0 ha'b'4 hd_a'4 hd_b'4 hd_cl
  have hcentre_pos : 0 < (centreSet Γ a'.1 b'.1 d.1).ncard := by
    rw [hcentre_card]; omega
  obtain ⟨e, he⟩ := (Set.ncard_pos (s := centreSet Γ a'.1 b'.1 d.1)).mp hcentre_pos
  have heT : e ∈ traceSet Γ a'.1 b'.1 := he.1
  have hde : Γ.dist d.1 e = 2 := he.2
  have he_not_span : e ∉ spanSet Γ u v := by
    intro hes
    have het : e ∈ traceSet Γ a.1 b.1 := hspan_trace hes
    have hde_ne : d.1 ≠ e := by
      intro h
      rw [h] at hde
      simp at hde
    have hde4 : Γ.dist d.1 e = 4 :=
      dist_eq_four_of_mem_trace hP hab4 hd_trace' het hde_ne
    omega
  let Vl : V := commonNeighbor hP hde
  have hdV : Γ.Adj Vl d.1 := (commonNeighbor_adj_left hP hde).symm
  have heV : Γ.Adj Vl e := (commonNeighbor_adj_right hP hde).symm
  have hV1 : c Vl = 1 := color_eq_one_of_adj_of_color_eq_zero hd0 (commonNeighbor_adj_left hP hde)
  have hu_trace : u ∈ traceSet Γ a.1 b.1 :=
    ⟨by simpa [SimpleGraph.dist_comm] using ha_trace.1,
      by simpa [SimpleGraph.dist_comm] using hb_trace.1⟩
  have hv_trace : v ∈ traceSet Γ a.1 b.1 :=
    ⟨by simpa [SimpleGraph.dist_comm] using ha_trace.2,
      by simpa [SimpleGraph.dist_comm] using hb_trace.2⟩
  have hu_trace' : u ∈ traceSet Γ a'.1 b'.1 :=
    ⟨by simpa [SimpleGraph.dist_comm] using ha'_trace.1,
      by simpa [SimpleGraph.dist_comm] using hb'_trace.1⟩
  have hv_trace' : v ∈ traceSet Γ a'.1 b'.1 :=
    ⟨by simpa [SimpleGraph.dist_comm] using ha'_trace.2,
      by simpa [SimpleGraph.dist_comm] using hb'_trace.2⟩
  have hdu_ne : d.1 ≠ u := by
    intro h
    exact huP' (h ▸ hdP)
  have huV : ¬ Γ.Adj u Vl := by
    intro hAdj
    have hdu2 : Γ.dist d.1 u = 2 := by
      have h := dist_eq_two_of_adj_of_adj_of_ne hP hAdj (commonNeighbor_adj_left hP hde).symm
        (by intro h; exact hdu_ne h.symm)
      rwa [SimpleGraph.dist_comm] at h
    have hdu4 : Γ.dist d.1 u = 4 :=
      dist_eq_four_of_mem_trace hP hab4 hd_trace' hu_trace hdu_ne
    omega
  have hdv_ne : d.1 ≠ v := by
    intro h
    exact hvP' (h ▸ hdP)
  have hvV : ¬ Γ.Adj v Vl := by
    intro hAdj
    have hdv2 : Γ.dist d.1 v = 2 := by
      have h := dist_eq_two_of_adj_of_adj_of_ne hP hAdj (commonNeighbor_adj_left hP hde).symm
        (by intro h; exact hdv_ne h.symm)
      rwa [SimpleGraph.dist_comm] at h
    have hdv4 : Γ.dist d.1 v = 4 :=
      dist_eq_four_of_mem_trace hP hab4 hd_trace' hv_trace hdv_ne
    omega
  have hdu3 : Γ.dist u Vl = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c huV (by rw [hu0, hV1]; decide)
  have hdv3 : Γ.dist v Vl = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hvV (by rw [hv0, hV1]; decide)
  let p : V := proj hP hdu3
  have hpV : Γ.Adj Vl p := proj_adj hP hdu3
  have hup : Γ.dist u p = 2 := proj_dist hP hdu3
  let R : V := commonNeighbor hP hup
  have huR : Γ.Adj u R := commonNeighbor_adj_left hP hup
  have hpR : Γ.Adj p R := commonNeighbor_adj_right hP hup
  let q0 : V := proj hP hdv3
  have hqV : Γ.Adj Vl q0 := proj_adj hP hdv3
  have hvq : Γ.dist v q0 = 2 := proj_dist hP hdv3
  let N : V := commonNeighbor hP hvq
  have hvN : Γ.Adj v N := commonNeighbor_adj_left hP hvq
  have hqN : Γ.Adj q0 N := commonNeighbor_adj_right hP hvq
  have hR1 : c R = 1 := color_eq_one_of_adj_of_color_eq_zero hu0 huR
  have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hv0 hvN
  have hRV_ne : R ≠ Vl := by
    intro h
    exact huV (by rw [← h]; exact huR)
  have hNV_ne : N ≠ Vl := by
    intro h
    exact hvV (by rw [← h]; exact hvN)
  have hRN_ne : R ≠ N := by
    intro h
    have h1 : Γ.Adj u R := huR
    have h2 : Γ.Adj v R := by rw [h]; exact hvN
    have huv2 : Γ.dist u v = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP h1 h2.symm (by
        intro h'; rw [h'] at huv; simp at huv)
    omega
  have hup_ne : u ≠ p := by
    intro h
    exact huV (by rw [h]; exact hpV.symm)
  have hRV2 : Γ.dist R Vl = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hpR.symm hpV.symm hRV_ne
  have hvq_ne : v ≠ q0 := by
    intro h
    exact hvV (by rw [h]; exact hqV.symm)
  have hNV2 : Γ.dist N Vl = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hqN.symm hqV.symm hNV_ne
  have hnot : ¬ ∃ h, Γ.Adj R h ∧ Γ.Adj N h := by
    rintro ⟨h, hRh, hNh⟩
    have hRN2 : Γ.dist R N = 2 := dist_eq_two_of_adj_of_adj_of_ne hP hRh hNh.symm hRN_ne
    obtain ⟨w, hw, huniq⟩ :=
      existsUnique_commonNeighbor_of_pairwise_dist_two hP hRN2 hRV2 hNV2
    have hwh : h = w := (existsUnique_commonNeighbor hP hRN2).unique ⟨hRh, hNh⟩
      ⟨hw.1, hw.2.1⟩
    have hhV : Γ.Adj Vl h := by rw [hwh]; exact hw.2.2
    have hhp : h = p := by
      by_contra hne
      exact hRV_ne (eq_of_adj_of_adj_of_adj hP hpR.symm hpV hRh hhV
        (fun h' => hne h'.symm))
    have hhq : h = q0 := by
      by_contra hne
      exact hNV_ne (eq_of_adj_of_adj_of_adj hP hqN.symm hqV hNh hhV
        (fun h' => hne h'.symm))
    have hpq : p = q0 := hhp.symm.trans hhq
    have h_trace : h ∈ traceSet Γ u v := by
      refine ⟨by rw [hhp]; exact hup, by rw [hhq]; exact hvq⟩
    have hh0 : c h = 0 := color_eq_zero_of_dist_eq_two hP hu0 h_trace.1
    have hdh : Γ.dist h d.1 = 2 := by
      have hne : h ≠ d.1 := by
        intro hhd
        have hdR : Γ.Adj R d.1 := by rw [← hhd, hhp]; exact hpR.symm
        have hdu2 : Γ.dist d.1 u = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP hdR.symm huR.symm hdu_ne
        have hdu4 : Γ.dist d.1 u = 4 :=
          dist_eq_four_of_mem_trace hP hab4 hd_trace' hu_trace hdu_ne
        omega
      exact dist_eq_two_of_adj_of_adj_of_ne hP hhV.symm hdV hne
    have heh : Γ.dist h e = 2 := by
      have hne : h ≠ e := by
        intro hhe
        have heR : Γ.Adj R e := by rw [← hhe, hhp]; exact hpR.symm
        have heu2 : Γ.dist e u = 2 := by
          exact dist_eq_two_of_adj_of_adj_of_ne hP heR.symm huR.symm (by
            intro h; exact he_not_span (by rw [h]; exact left_mem_spanSet huv))
        have heu4 : Γ.dist e u = 4 :=
          dist_eq_four_of_mem_trace hP ha'b'4 heT hu_trace' (by
            intro h; exact he_not_span (by rw [h]; exact left_mem_spanSet huv))
        omega
      exact dist_eq_two_of_adj_of_adj_of_ne hP hhV.symm heV hne
    have hd_not_span : d.1 ∉ spanSet Γ u v := fun h => hspan_disj d.1 h hdP
    have hlarge : q + 1 < {w | w ∈ traceSet Γ a.1 b.1 ∧ Γ.dist h w = 2}.ncard := by
      have hsub : insert d.1 (spanSet Γ u v) ⊆
          {w | w ∈ traceSet Γ a.1 b.1 ∧ Γ.dist h w = 2} := by
        intro w hw
        rcases hw with rfl | hw
        · exact ⟨hd_trace', by simpa [SimpleGraph.dist_comm] using hdh⟩
        · refine ⟨hspan_trace hw, ?_⟩
          rw [SimpleGraph.dist_comm]
          exact dist_eq_two_of_mem_span_of_mem_trace hP hΓ.thick huv hw h_trace
      have hcard : (insert d.1 (spanSet Γ u v)).ncard = q + 2 := by
        rw [Set.insert_eq, Set.ncard_union_eq (Set.disjoint_singleton_left.mpr hd_not_span),
          Set.ncard_singleton, hΓ.span u v hu0 huv]
        omega
      calc q + 1 < q + 2 := by omega
        _ = (insert d.1 (spanSet Γ u v)).ncard := hcard.symm
        _ ≤ _ := Set.ncard_le_ncard hsub
    have hspan_ab : h ∈ spanSet Γ a.1 b.1 :=
      mem_spanSet_of_ncard_traceSet_inter_neighborSet hΓ ha0 hab4 hh0 hlarge
    have hlarge' : q + 1 < {w | w ∈ traceSet Γ a'.1 b'.1 ∧ Γ.dist h w = 2}.ncard := by
      have hsub : insert e (spanSet Γ u v) ⊆
          {w | w ∈ traceSet Γ a'.1 b'.1 ∧ Γ.dist h w = 2} := by
        intro w hw
        rcases hw with rfl | hw
        · exact ⟨heT, by simpa [SimpleGraph.dist_comm] using heh⟩
        · refine ⟨hspan_trace' hw, ?_⟩
          rw [SimpleGraph.dist_comm]
          exact dist_eq_two_of_mem_span_of_mem_trace hP hΓ.thick huv hw h_trace
      have hcard : (insert e (spanSet Γ u v)).ncard = q + 2 := by
        rw [Set.insert_eq, Set.ncard_union_eq (Set.disjoint_singleton_left.mpr he_not_span),
          Set.ncard_singleton, hΓ.span u v hu0 huv]
        omega
      calc q + 1 < q + 2 := by omega
        _ = (insert e (spanSet Γ u v)).ncard := hcard.symm
        _ ≤ _ := Set.ncard_le_ncard hsub
    have hspan_ab' : h ∈ spanSet Γ a'.1 b'.1 :=
      mem_spanSet_of_ncard_traceSet_inter_neighborSet hΓ ha'0 ha'b'4 hh0 hlarge'
    have hmemL : h ∈ Subtype.val '' L := by rwa [hLspan]
    obtain ⟨t, htL, hth⟩ := hmemL
    have hmemL' : h ∈ Subtype.val '' L' := by rwa [hL'span]
    obtain ⟨t', htL', ht'h⟩ := hmemL'
    have htt' : t = t' := Subtype.ext (by rw [hth, ht'h])
    exact (Set.disjoint_left.mp hdisj htL) (htt' ▸ htL')
  have hRN_opp : Γ.dist R N = 4 := by
    have hcRN : c R = c N := by rw [hR1, hN1]
    have heven : Even (Γ.dist R N) := (hP.eq_iff_even_dist c R N).1 hcRN
    have hne0 : Γ.dist R N ≠ 0 := by
      intro h0
      exact hRN_ne ((hP.connected.dist_eq_zero_iff).mp h0)
    have hne2 : Γ.dist R N ≠ 2 := by
      intro h2
      obtain ⟨h, hh, -⟩ := existsUnique_commonNeighbor hP h2
      exact hnot ⟨h, hh.1, hh.2⟩
    have hle4 : Γ.dist R N ≤ 4 := by
      have h1 : Γ.dist R Vl ≤ 2 := by
        have htri := hP.connected.dist_triangle (u := R) (v := p) (w := Vl)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hpR.symm,
          SimpleGraph.dist_eq_one_iff_adj.mpr hpV.symm] at htri
        omega
      have h2 : Γ.dist Vl N ≤ 2 := by
        have htri := hP.connected.dist_triangle (u := Vl) (v := q0) (w := N)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hqV,
          SimpleGraph.dist_eq_one_iff_adj.mpr hqN] at htri
        omega
      have htri := hP.connected.dist_triangle (u := R) (v := Vl) (w := N)
      omega
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨P'', ⟨hP''F, hRP'', hNP''⟩, -⟩ := existsUnique_fullSubquadrangle hΓ hR1 hRN_opp
  have huP'' : u ∈ P'' := hRP'' huR.symm
  have hvP'' : v ∈ P'' := hNP'' hvN.symm
  have hpP'' : p ∈ P'' := hRP'' hpR.symm
  have hqP'' : q0 ∈ P'' := hNP'' hqN.symm
  have hpq : p ≠ q0 := by
    intro hpq
    exact hnot ⟨p, hpR.symm, by rw [hpq]; exact hqN.symm⟩
  have hVP'' : Γ.neighborSet Vl ⊆ P'' := by
    apply hP''F.2.1 Vl hV1
    have h2 : 1 < (Γ.neighborSet Vl ∩ P'').ncard := by
      rw [Set.one_lt_ncard]
      exact ⟨p, ⟨hpV, hpP''⟩, q0, ⟨hqV, hqP''⟩, hpq⟩
    omega
  have hdP'' : d.1 ∈ P'' := hVP'' hdV
  have heP'' : e ∈ P'' := hVP'' heV
  have hLperp_P'' : traceSet Γ a.1 b.1 ⊆ P'' :=
    traceSet_subset_of_isFullSubquadrangle hΓ hP''F ha0 hab4
      ⟨hu_trace, huP''⟩ ⟨hv_trace, hvP''⟩ ⟨hd_trace', hdP''⟩
      huv_ne (fun h => hspan_disj d.1 h hdP)
  have hL'perp_P'' : traceSet Γ a'.1 b'.1 ⊆ P'' :=
    traceSet_subset_of_isFullSubquadrangle hΓ hP''F ha'0 ha'b'4
      ⟨hu_trace', huP''⟩ ⟨hv_trace', hvP''⟩ ⟨heT, heP''⟩
      huv_ne he_not_span
  have hPcard : P'.ncard = (q ^ 2 + 1) * (q ^ 2 * q + 1) :=
    ncard_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF
  have hP''card : P''.ncard = (q ^ 2 + 1) * (q ^ 2 * q + 1) :=
    ncard_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hP''F
  have hspanP'' : spanSet Γ u v ⊆ P'' :=
    spanSet_subset_of_isFullSubquadrangle hΓ hP''F huP'' hvP'' huv
  have hne : P' ∩ P'' ≠ P' := by
    intro heq
    have hsub : P' ⊆ P'' := by
      intro x hx
      have hx' : x ∈ P' ∩ P'' := by rw [heq]; exact hx
      exact hx'.2
    have heq' : P' = P'' :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hP''card, hPcard])
    have hpos : 0 < (spanSet Γ u v).ncard := by
      rw [hΓ.span u v hu0 huv]; omega
    obtain ⟨w, hw⟩ := (Set.ncard_pos (s := spanSet Γ u v)).mp hpos
    exact hspan_disj w hw (heq'.symm ▸ hspanP'' hw)
  have hproper : ∃ w, w ∈ P' ∧ w ∉ P'' := by
    by_contra h
    push Not at h
    have hsub : P' ⊆ P' ∩ P'' := fun x hx => ⟨hx, h x hx⟩
    exact hne (Set.Subset.antisymm hsub Set.inter_subset_left).symm
  obtain ⟨w0, hw0P', hw0P''⟩ := hproper
  have hw0S : w0 ∈ subquadrangleSet Γ c P' := mem_subquadrangleSet.mpr (Or.inl hw0P')
  let w : subquadrangleSet Γ c P' := ⟨w0, hw0S⟩
  have hw0 : subquadrangleColoring c P' w = 0 := by
    rw [subquadrangleColoring_apply]; exact hF.1 w0 hw0P'
  have hwX : w ∉ {z : subquadrangleSet Γ c P' | z.1 ∈ P' ∩ P''} := by
    intro hz
    exact hw0P'' hz.2
  let X : Set (subquadrangleSet Γ c P') := {z | z.1 ∈ P' ∩ P''}
  have hXlin : IsLinearVariety (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [subquadrangleColoring_apply]
      exact hF.1 z.1 hz.1
    · intro z hz z' hz' hzz' v0 hv0
      rw [show X = {t : subquadrangleSet Γ c P' | t.1 ∈ P' ∩ P''} from rfl]
      by_cases h2 : (Γ.induce (subquadrangleSet Γ c P')).dist z z' = 2
      ·
        have hzP : z.1 ∈ P' := hz.1
        have hz'P : z'.1 ∈ P' := hz'.1
        have hzP'' : z.1 ∈ P'' := hz.2
        have hz'P'' : z'.1 ∈ P'' := hz'.2
        have hz0 : c z.1 = 0 := hF.1 z.1 hzP
        have hzz'_ne : z.1 ≠ z'.1 := by
          intro h; exact hzz' (Subtype.ext h)
        have hline : starLine (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') z z' =
            (Γ.induce (subquadrangleSet Γ c P')).neighborSet
              (commonNeighbor hP' h2) :=
          starLine_eq_neighborSet hP' hT' (subquadrangleColoring c P')
            (by rw [subquadrangleColoring_apply]; exact hF.1 z.1 hzP) h2
        rw [hline] at hv0
        have hL0 : c (commonNeighbor hP' h2).1 = 1 := by
          rw [← subquadrangleColoring_apply]
          exact color_eq_one_of_adj_of_color_eq_zero
            (by simpa [subquadrangleColoring_apply] using hF.1 z.1 hzP)
            (commonNeighbor_adj_left hP' h2)
        have hL0amb : Γ.neighborSet (commonNeighbor hP' h2).1 ⊆ P' := by
          apply hF.2.1 (commonNeighbor hP' h2).1
          · rw [← subquadrangleColoring_apply]; exact hL0
          · have h2' : 1 < (Γ.neighborSet (commonNeighbor hP' h2).1 ∩ P').ncard := by
              rw [Set.one_lt_ncard]
              exact ⟨z.1, ⟨(SimpleGraph.induce_adj.mp (commonNeighbor_adj_left hP' h2)).symm,
                hzP⟩,
                z'.1, ⟨(SimpleGraph.induce_adj.mp (commonNeighbor_adj_right hP' h2)).symm, hz'P⟩,
                hzz'_ne⟩
            omega
        have hL0amb'' : Γ.neighborSet (commonNeighbor hP' h2).1 ⊆ P'' := by
          apply hP''F.2.1 (commonNeighbor hP' h2).1
          · rw [← subquadrangleColoring_apply]; exact hL0
          · have h2' : 1 < (Γ.neighborSet (commonNeighbor hP' h2).1 ∩ P'').ncard := by
              rw [Set.one_lt_ncard]
              exact ⟨z.1, ⟨(SimpleGraph.induce_adj.mp (commonNeighbor_adj_left hP' h2)).symm,
                hzP''⟩,
                z'.1, ⟨(SimpleGraph.induce_adj.mp (commonNeighbor_adj_right hP' h2)).symm,
                  hz'P''⟩, hzz'_ne⟩
            omega
        have hv0 : v0.1 ∈ Γ.neighborSet (commonNeighbor hP' h2).1 :=
          SimpleGraph.induce_adj.mp hv0
        exact ⟨hL0amb hv0, hL0amb'' hv0⟩
      ·
        have h4 : (Γ.induce (subquadrangleSet Γ c P')).dist z z' = 4 := by
          rcases dist_eq_two_or_four_of_color_zero hP'
            (by rw [subquadrangleColoring_apply]; exact hF.1 z.1 hz.1)
            (by rw [subquadrangleColoring_apply]; exact hF.1 z'.1 hz'.1) hzz' with h | h
          · exact absurd h h2
          · exact h
        have hzP : z.1 ∈ P' := hz.1
        have hz'P : z'.1 ∈ P' := hz'.1
        have h4amb : Γ.dist z.1 z'.1 = 4 := by
          have h := h4
          rwa [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF
            z.2 z'.2] at h
        have hline : starLine (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') z z' =
            spanSet (Γ.induce (subquadrangleSet Γ c P')) z z' :=
          starLine_eq_spanSet hP' hT' (subquadrangleColoring c P')
            (by rw [subquadrangleColoring_apply]; exact hF.1 z.1 hzP) h4
        rw [hline] at hv0
        have hv0 : v0.1 ∈ spanSet Γ z.1 z'.1 := by
          have hv0img : v0.1 ∈ Subtype.val '' spanSet (Γ.induce (subquadrangleSet Γ c P')) z z' :=
            ⟨v0, hv0, rfl⟩
          rwa [spanSet_subquadrangle hΓ hF
            (by rw [subquadrangleColoring_apply]; exact hF.1 z.1 hzP) h4amb] at hv0img
        exact ⟨spanSet_subset_of_isFullSubquadrangle hΓ hF hzP hz'P h4amb hv0,
          spanSet_subset_of_isFullSubquadrangle hΓ hP''F hz.2 hz'.2 h4amb hv0⟩
  have hXproper : IsProperVariety (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') X :=
    ⟨hXlin, ⟨w, hw0, hwX⟩⟩
  refine ⟨X, hXproper, ?_⟩
  intro z hz
  rcases hz with hz | hz
  ·
    have hzT : z.1 ∈ traceSet Γ a.1 b.1 := hd_trace z hz
    exact ⟨hd_P z hz, hLperp_P'' hzT⟩
  ·
    have hzT : z.1 ∈ traceSet Γ a'.1 b'.1 := by
      have hzimg : z.1 ∈ Subtype.val '' ptPerp (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') L' := ⟨z, hz, rfl⟩
      rw [ptPerp_subquadrangle hΓ hF, hL'span] at hzimg
      have h := hzimg.1
      rw [← starLine_eq_spanSet hP hΓ.thick c ha'0 ha'b'4] at h
      rwa [ptPerp_starLine_eq_traceSet hP hΓ.thick c ha'0 ha'b'4] at h
    exact ⟨hd_P' z hz, hL'perp_P'' hzT⟩

theorem talliniCond_subquadrangle (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) :
    TalliniCond (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hΓ.thick c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hΓ.thick c hΓ.deg hF hΓ.two_le
  have hdeg' : ∀ w : subquadrangleSet Γ c P',
      (Γ.induce (subquadrangleSet Γ c P')).degree w =
        if subquadrangleColoring c P' w = 0 then q + 1 else q ^ 2 + 1 :=
    fun w => degree_subquadrangleGraph hΓ hF w
  have hreg' : ∀ w : subquadrangleSet Γ c P', subquadrangleColoring c P' w = 0 →
      IsRegularVertex (Γ.induce (subquadrangleSet Γ c P')) w :=
    fun w hw => isRegularVertex_subquadrangle hΓ hF w hw
  intro L L' hL hL' hvar
  obtain ⟨X, hXproper, hLX⟩ := hvar
  have hLX1 : L ⊆ X := fun a ha => hLX (Or.inl ha)
  have hLX2 : L' ⊆ X := fun a ha => hLX (Or.inr ha)
  by_cases hLL : L = L'
  ·
    have hpos : 0 < L.ncard := by
      have := one_lt_ncard_of_isStarLine hL
      omega
    obtain ⟨z, hzL⟩ := (Set.ncard_pos (s := L)).mp hpos
    have hz0 : subquadrangleColoring c P' z = 0 := color_eq_zero_of_mem_isStarLine hL hzL
    refine ⟨ptPerp (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') {z},
      (isStarPlane_ptPerp_singleton hP' hT' (subquadrangleColoring c P')
        (s := q ^ 2) (t := q) hdeg' hz0).1, ?_⟩
    rw [← hLL]
    intro w hw
    rcases hw with hw | hw
    · rw [mem_ptPerp] at hw ⊢
      exact ⟨hw.1, fun a ha => by
        rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact hw.2 z hzL⟩
    · rw [mem_ptPerp] at hw ⊢
      exact ⟨hw.1, fun a ha => by
        rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact hw.2 z hzL⟩
  ·
    have hXplane : IsStarPlane (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') X :=
      isStarPlane_of_isProperVariety hΓ hF hXproper hL hL' hLX1 hLX2 hLL
    rcases isStarPlane_cases hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q)
      hdeg' hreg' hXplane with habs | hnon
    ·
      obtain ⟨u, hu0, rfl⟩ := habs
      have huL : u ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') L := by
        rw [mem_ptPerp]
        refine ⟨hu0, fun a ha => ?_⟩
        have haX : a ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') {u} := hLX1 ha
        rw [mem_ptPerp] at haX
        rw [SimpleGraph.dist_comm]
        exact haX.2 u (Set.mem_singleton u)
      have huL' : u ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') L' := by
        rw [mem_ptPerp]
        refine ⟨hu0, fun a ha => ?_⟩
        have haX : a ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') {u} := hLX2 ha
        rw [mem_ptPerp] at haX
        rw [SimpleGraph.dist_comm]
        exact haX.2 u (Set.mem_singleton u)
      have hMstar : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') (ptPerp (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') L) :=
        (ptPerp_ptPerp_starLine hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q)
          hdeg' hreg' hL).1
      have hM'star : IsStarLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') (ptPerp (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') L') :=
        (ptPerp_ptPerp_starLine hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q)
          hdeg' hreg' hL').1
      exact exists_isProperVariety_of_common_mem hΓ hF hMstar hM'star huL huL'
    ·
      by_cases hmeet : (L ∩ L').Nonempty
      ·
        obtain ⟨z, hzL, hzL'⟩ := hmeet
        have hz0 : subquadrangleColoring c P' z = 0 :=
          color_eq_zero_of_mem_isStarLine hL hzL
        refine ⟨ptPerp (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') {z},
          (isStarPlane_ptPerp_singleton hP' hT' (subquadrangleColoring c P')
            (s := q ^ 2) (t := q) hdeg' hz0).1, ?_⟩
        intro w hw
        rcases hw with hw | hw
        · rw [mem_ptPerp] at hw ⊢
          exact ⟨hw.1, fun a ha => by
            rw [Set.mem_singleton_iff] at ha
            rw [ha]
            exact hw.2 z hzL⟩
        · rw [mem_ptPerp] at hw ⊢
          exact ⟨hw.1, fun a ha => by
            rw [Set.mem_singleton_iff] at ha
            rw [ha]
            exact hw.2 z hzL'⟩
      ·
        have hdisj : Disjoint L L' :=
          Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hmeet)
        exact exists_isProperVariety_of_disjoint hΓ hF hL hL' hdisj hnon hLX1 hLX2

end CFSG.Geometry.GeneralizedQuadrangles

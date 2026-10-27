module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.SubquadrangleTallini
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.PlanesThrough

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

private theorem not_isOvoid_of_isAbsPlane (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {Y : Set (subquadrangleSet Γ c P')}
    (hY : IsAbsPlane (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') Y) :
    ¬ IsOvoid (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') Y := by
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
  intro hOvoid
  obtain ⟨u, hu0, rfl⟩ := hY
  have h1 : (ptPerp (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') {u}).ncard = q ^ 2 * q + 1 :=
    ncard_of_isOvoid hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q) hdeg' hOvoid
  have h2 : (ptPerp (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') {u}).ncard = q ^ 2 * q + q ^ 2 + 1 :=
    ncard_ptPerp_singleton hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q) hdeg' hu0
  rw [h1] at h2
  have hq : 0 < q ^ 2 := pow_pos (show 0 < q by have h := hΓ.two_le; omega) 2
  omega

theorem isAbsPlane_subquadrangle_iff (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {X : Set (subquadrangleSet Γ c P')} :
    IsAbsPlane (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') X ↔
      ∃ x ∈ P', Subtype.val '' X = ptPerp Γ c {x} ∩ P' := by
  constructor
  · rintro ⟨u, hu0, rfl⟩
    refine ⟨u.1, mem_P'_of_subquadrangleColoring_eq_zero hu0, ?_⟩
    rw [ptPerp_subquadrangle hΓ hF]
    rw [show Subtype.val '' ({u} : Set (subquadrangleSet Γ c P')) = {u.1} from by
      ext w
      simp]
  · rintro ⟨x, hxP, hX⟩
    have hxS : x ∈ subquadrangleSet Γ c P' := mem_subquadrangleSet.mpr (Or.inl hxP)
    let u : subquadrangleSet Γ c P' := ⟨x, hxS⟩
    refine ⟨u, ?_, ?_⟩
    · rw [subquadrangleColoring_apply]; exact hF.1 x hxP
    · have h := ptPerp_subquadrangle hΓ hF ({u} : Set (subquadrangleSet Γ c P'))
      rw [show Subtype.val '' ({u} : Set (subquadrangleSet Γ c P')) = {x} from by
        ext w
        simp [u]] at h
      ext z
      constructor
      · intro hz
        have hzimg : z.1 ∈ Subtype.val '' X := ⟨z, hz, rfl⟩
        rw [hX] at hzimg
        have : z.1 ∈ Subtype.val '' ptPerp (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') {u} := by
          rw [h]; exact hzimg
        obtain ⟨a, ha, hav⟩ := this
        have haz : a = z := Subtype.ext hav
        rwa [haz] at ha
      · intro hz
        have hzimg : z.1 ∈ Subtype.val '' ptPerp (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') {u} := ⟨z, hz, rfl⟩
        rw [h] at hzimg
        have hzX : z.1 ∈ Subtype.val '' X := by rw [hX]; exact hzimg
        obtain ⟨a, ha, hav⟩ := hzX
        have haz : a = z := Subtype.ext hav
        rwa [haz] at ha

theorem isNonabsPlane_subquadrangle_iff (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {X : Set (subquadrangleSet Γ c P')} :
    IsNonabsPlane (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') X ↔
      ∃ y z, c y = 0 ∧ Γ.dist y z = 4 ∧ traceSet Γ y z ⊆ P' ∧
        Subtype.val '' X = traceSet Γ y z := by
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
  constructor
  · rintro ⟨hplane, hovoid⟩
    have hXcard : X.ncard = q ^ 3 + 1 := by
      rw [ncard_of_isOvoid hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q)
        hdeg' hovoid]
      ring
    have hpos : 0 < X.ncard := by rw [hXcard]; positivity
    obtain ⟨x', hx'X⟩ := (Set.ncard_pos (s := X)).mp hpos
    have h2 : 1 < X.ncard := by
      rw [hXcard]
      have hq : 0 < q := by have h := hΓ.two_le; omega
      have hq3 : 0 < q ^ 3 := by positivity
      omega
    obtain ⟨y', hy'X, hy'ne⟩ := Set.exists_ne_of_one_lt_ncard h2 x'
    have hx'0 : subquadrangleColoring c P' x' = 0 := hovoid.1 x' hx'X
    have hy'0 : subquadrangleColoring c P' y' = 0 := hovoid.1 y' hy'X
    have hx'y' : x' ≠ y' := hy'ne.symm
    have hxy'4 : (Γ.induce (subquadrangleSet Γ c P')).dist x' y' = 4 :=
      dist_eq_four_of_mem_of_isOvoid hP' hT' hovoid hx'X hy'X hx'y'
    have hxy4 : Γ.dist x'.1 y'.1 = 4 := by
      have h := hxy'4
      rwa [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF x'.2 y'.2]
        at h
    have hx'P : x'.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hx'0
    have hspan_card : (spanSet (Γ.induce (subquadrangleSet Γ c P')) x' y').ncard = q + 1 := by
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective,
        spanSet_subquadrangle hΓ hF hx'0 hxy4]
      exact hΓ.span x'.1 y'.1 (hF.1 x'.1 hx'P) hxy4
    have hlt : (spanSet (Γ.induce (subquadrangleSet Γ c P')) x' y').ncard < X.ncard := by
      rw [hspan_card, hXcard]
      have hq : 2 ≤ q := hΓ.two_le
      have hqpos : 0 < q := by omega
      have h1 : q + 1 ≤ q ^ 2 := by
        calc q + 1 ≤ q + q := by omega
          _ = 2 * q := by ring
          _ ≤ q * q := Nat.mul_le_mul_right q hq
          _ = q ^ 2 := by ring
      have h2 : q ^ 2 ≤ q ^ 3 := by
        calc q ^ 2 = q ^ 2 * 1 := (Nat.mul_one _).symm
          _ ≤ q ^ 2 * q := Nat.mul_le_mul_left _ hqpos
          _ = q ^ 3 := by ring
      omega
    obtain ⟨z', hz'X, hz'span⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    have hz'0 : subquadrangleColoring c P' z' = 0 := hovoid.1 z' hz'X
    have hzspan : z'.1 ∉ spanSet Γ x'.1 y'.1 := by
      intro h
      have hzimg : z'.1 ∈ Subtype.val '' spanSet (Γ.induce (subquadrangleSet Γ c P'))
          x' y' := by
        rw [spanSet_subquadrangle hΓ hF hx'0 hxy4]
        exact h
      obtain ⟨a, ha, hav⟩ := hzimg
      have haz : a = z' := Subtype.ext hav
      exact hz'span (haz ▸ ha)
    have hnc : ¬ IsStarCollinear (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') x' y' z' := by
      rintro ⟨M, hM, hxM, hyM, hzM⟩
      have hMxy : M = starLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') x' y' :=
        starLine_eq_of_isStarLine_of_mem hP' hT' hM hxM hyM hx'y'
      have hzstar : z' ∈ starLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') x' y' := by rwa [hMxy] at hzM
      have hzspan' : z' ∈ spanSet (Γ.induce (subquadrangleSet Γ c P')) x' y' := by
        rwa [starLine_eq_spanSet hP' hT' (subquadrangleColoring c P') hx'0 hxy'4] at hzstar
      exact hz'span hzspan'
    have hzcl : z'.1 ∉ clSet Γ x'.1 y'.1 := by
      intro hcl
      obtain ⟨u, hu0, hxu, hyu, hzu⟩ :=
        exists_ptPerp_of_mem_clSet hΓ hF hx'0 hy'0 hz'0 hxy4 hcl hzspan
      have hPplane : IsStarPlane (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') (ptPerp (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') {u}) :=
        isStarPlane_ptPerp_singleton hP' hT' (subquadrangleColoring c P')
          (s := q ^ 2) (t := q) hdeg' hu0
      have heq : X = ptPerp (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') {u} :=
        eq_of_isStarPlane hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q)
          hdeg' hreg' hplane hPplane ⟨hx'X, hxu⟩ ⟨hy'X, hyu⟩ ⟨hz'X, hzu⟩ hnc
      exact (not_isOvoid_of_isAbsPlane hΓ hF ⟨u, hu0, heq⟩) hovoid
    obtain ⟨u, v, hu0, huv, hTP, hxu, hyu, hzu⟩ :=
      exists_traceSet_of_not_mem_clSet hΓ hF hx'0 hy'0 hz'0 hxy4 hzcl
    refine ⟨u, v, hu0, huv, hTP, ?_⟩
    have hplaneT : IsStarPlane (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') (subquadrangleTrace Γ c P' u v) :=
      isStarPlane_subquadrangleTrace hΓ hF hu0 huv hTP hxu hyu hzu hnc
    have heq : X = subquadrangleTrace Γ c P' u v :=
      eq_of_isStarPlane hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q)
        hdeg' hreg' hplane hplaneT ⟨hx'X, hxu⟩ ⟨hy'X, hyu⟩ ⟨hz'X, hzu⟩ hnc
    rw [heq, val_image_subquadrangleTrace hΓ hF hTP]
  · rintro ⟨y, z, hy0, hyz, hTP, hval⟩
    have hTcard : (traceSet Γ y z).ncard = q ^ 3 + 1 := by
      rw [ncard_trace hP hyz, hΓ.deg y, if_pos hy0]
    have hXcard : X.ncard = q ^ 3 + 1 := by
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective, hval, hTcard]
    have hXeq : X = subquadrangleTrace Γ c P' y z := by
      ext w
      constructor
      · intro hw
        have hw' : w.1 ∈ Subtype.val '' X := ⟨w, hw, rfl⟩
        rw [hval] at hw'
        exact hw'
      · intro hw
        have hw' : w.1 ∈ Subtype.val '' X := by rw [hval]; exact hw
        obtain ⟨a, ha, hav⟩ := hw'
        have haz : a = w := Subtype.ext hav
        rwa [haz] at ha
    rw [hXeq]
    have hpos : 0 < (traceSet Γ y z).ncard := by rw [hTcard]; positivity
    obtain ⟨a, haT⟩ := (Set.ncard_pos (s := traceSet Γ y z)).mp hpos
    have h2 : 1 < (traceSet Γ y z).ncard := by
      rw [hTcard]
      have hq : 0 < q := by have h := hΓ.two_le; omega
      have hq3 : 0 < q ^ 3 := by positivity
      omega
    obtain ⟨b, hbT, hba⟩ := Set.exists_ne_of_one_lt_ncard h2 a
    have ha0 : c a = 0 := color_eq_zero_of_dist_eq_two hP hy0 haT.1
    have hab4 : Γ.dist a b = 4 := dist_eq_four_of_mem_trace hP hyz haT hbT hba.symm
    have hspan_card : (spanSet Γ a b).ncard = q + 1 := hΓ.span a b ha0 hab4
    have hlt : (spanSet Γ a b).ncard < (traceSet Γ y z).ncard := by
      rw [hspan_card, hTcard]
      have hq : 2 ≤ q := hΓ.two_le
      have hqpos : 0 < q := by omega
      have h1 : q + 1 ≤ q ^ 2 := by
        calc q + 1 ≤ q + q := by omega
          _ = 2 * q := by ring
          _ ≤ q * q := Nat.mul_le_mul_right q hq
          _ = q ^ 2 := by ring
      have h2 : q ^ 2 ≤ q ^ 3 := by
        calc q ^ 2 = q ^ 2 * 1 := (Nat.mul_one _).symm
          _ ≤ q ^ 2 * q := Nat.mul_le_mul_left _ hqpos
          _ = q ^ 3 := by ring
      omega
    obtain ⟨c0, hc0T, hc0span⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    have haP : a ∈ P' := hTP haT
    have hbP : b ∈ P' := hTP hbT
    have hc0P : c0 ∈ P' := hTP hc0T
    let a' : subquadrangleSet Γ c P' := ⟨a, mem_subquadrangleSet.mpr (Or.inl haP)⟩
    let b' : subquadrangleSet Γ c P' := ⟨b, mem_subquadrangleSet.mpr (Or.inl hbP)⟩
    let c' : subquadrangleSet Γ c P' := ⟨c0, mem_subquadrangleSet.mpr (Or.inl hc0P)⟩
    have ha'0 : subquadrangleColoring c P' a' = 0 := by
      rw [subquadrangleColoring_apply]; exact ha0
    have hb'0 : subquadrangleColoring c P' b' = 0 := by
      rw [subquadrangleColoring_apply]
      exact color_eq_zero_of_dist_eq_two hP hy0 hbT.1
    have hc'0 : subquadrangleColoring c P' c' = 0 := by
      rw [subquadrangleColoring_apply]
      exact color_eq_zero_of_dist_eq_two hP hy0 hc0T.1
    have ha'b' : a' ≠ b' := by
      intro h
      exact hba.symm (congrArg Subtype.val h)
    have hab4' : (Γ.induce (subquadrangleSet Γ c P')).dist a' b' = 4 := by
      rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF a'.2 b'.2,
        hab4]
    have hnc : ¬ IsStarCollinear (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') a' b' c' := by
      rintro ⟨M, hM, haM, hbM, hcM⟩
      have hMab : M = starLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') a' b' :=
        starLine_eq_of_isStarLine_of_mem hP' hT' hM haM hbM ha'b'
      have hcstar : c' ∈ starLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') a' b' := by rwa [hMab] at hcM
      have hcspan' : c' ∈ spanSet (Γ.induce (subquadrangleSet Γ c P')) a' b' := by
        rwa [starLine_eq_spanSet hP' hT' (subquadrangleColoring c P') ha'0 hab4'] at hcstar
      have hcimg : c0 ∈ Subtype.val '' spanSet (Γ.induce (subquadrangleSet Γ c P')) a' b' :=
        ⟨c', hcspan', rfl⟩
      rw [spanSet_subquadrangle hΓ hF ha'0 hab4] at hcimg
      exact hc0span hcimg
    refine ⟨?_, ?_⟩
    · exact isStarPlane_subquadrangleTrace hΓ hF hy0 hyz hTP haT hbT hc0T hnc
    · exact isOvoid_of_isLinearVariety hP' hT' (subquadrangleColoring c P')
        (s := q ^ 2) (t := q) hdeg' hreg'
        (isLinearVariety_subquadrangleTrace hΓ hF hy0 hyz)
        (pairwise_subquadrangleTrace hΓ hF hyz)
        ⟨a', haT, b', hbT, c', hc0T, hnc⟩

end CFSG.Geometry.GeneralizedQuadrangles

module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometrySemilinear
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryRealization
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module
  Submodule
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)

variable {r : ℕ} {K : Type*} [Field K]

section XEmb

variable (r K) in
@[expose] def xEmb : (Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) where
  toFun x := Sum.elim x 0
  map_add' _ _ := funext fun c => by rcases c with i | i <;> simp
  map_smul' _ _ := funext fun c => by rcases c with i | i <;> simp

theorem xEmb_apply (x : Fin r → K) : xEmb r K x = Sum.elim x 0 :=
  rfl

theorem xEmb_injective : Function.Injective (xEmb r K) := fun _ _ h =>
  funext fun i => congrFun h (Sum.inl i)

theorem range_xEmb : LinearMap.range (xEmb r K) = flag r K r := by
  ext v
  rw [LinearMap.mem_range, mem_flag_top_iff]
  constructor
  · rintro ⟨x, rfl⟩ i
    rfl
  · intro h
    refine ⟨fun i => v (Sum.inl i), funext fun c => ?_⟩
    rcases c with i | i
    · rfl
    · exact (h i).symm

theorem map_comap_xEmb {W : Submodule K (Fin r ⊕ Fin r → K)} (hW : W ≤ flag r K r) :
    (W.comap (xEmb r K)).map (xEmb r K) = W := by
  rw [Submodule.map_comap_eq, range_xEmb, inf_eq_right.2 hW]

theorem comap_map_xEmb (W : Submodule K (Fin r → K)) : (W.map (xEmb r K)).comap (xEmb r K) = W :=
  Submodule.comap_map_eq_of_injective xEmb_injective W

theorem finrank_map_xEmb (W : Submodule K (Fin r → K)) :
    finrank K (W.map (xEmb r K)) = finrank K W :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ xEmb_injective W)).symm

theorem finrank_comap_xEmb {W : Submodule K (Fin r ⊕ Fin r → K)} (hW : W ≤ flag r K r) :
    finrank K (W.comap (xEmb r K)) = finrank K W := by
  rw [← finrank_map_xEmb, map_comap_xEmb hW]

theorem map_xEmb_le (W : Submodule K (Fin r → K)) : W.map (xEmb r K) ≤ flag r K r := by
  rw [← range_xEmb]
  exact LinearMap.map_le_range

theorem sCoord_xEmb (σ : K ≃+* K) (x : Fin r → K) :
    sCoord σ (xEmb r K x) = xEmb r K (fun i => σ (x i)) :=
  funext fun c => by rcases c with i | i <;> simp [xEmb_apply]

theorem sCoordImage_map_xEmb (σ : K ≃+* K) (W : Submodule K (Fin r → K)) :
    sCoordImage σ (W.map (xEmb r K)) = (LinearFlag.coordImage σ W).map (xEmb r K) := by
  ext v
  rw [mem_sCoordImage, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, hxv⟩
    refine ⟨fun i => σ (x i), LinearFlag.coord_mem_coordImage hx, ?_⟩
    rw [← sCoord_xEmb, hxv, sCoord_sCoord_symm]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun i => σ.symm (y i), hy, ?_⟩
    rw [sCoord_xEmb]

theorem levi_xEmb (A : GL (Fin r) K) (x : Fin r → K) :
    levi r K A (xEmb r K x) = xEmb r K ((A : Matrix (Fin r) (Fin r) K) *ᵥ x) := by
  rw [levi_eq_matrixEquiv, matrixEquiv_apply, coe_leviGL, blockDiagInv, fromBlocks_mulVec_apply]
  funext c
  rcases c with i | i
  · simp [xEmb_apply, Function.comp_def]
  · simp [xEmb_apply, Function.comp_def, mulVec, dotProduct]

theorem levi_mem_ySpan (A : GL (Fin r) K) {v : Fin r ⊕ Fin r → K} (hv : v ∈ ySpan r K) :
    levi r K A v ∈ ySpan r K := by
  rw [mem_ySpan_iff] at hv ⊢
  intro i
  rw [levi_eq_matrixEquiv, matrixEquiv_apply, coe_leviGL, blockDiagInv, fromBlocks_mulVec_apply]
  have : (fun j => v (Sum.inl j)) = 0 := funext hv
  simp only [Sum.elim_inl, Function.comp_def, this, mulVec_zero, zero_add, Matrix.zero_mulVec]
  rfl

theorem semiImage_map_xEmb (A : GL (Fin r) K) (σ : K ≃+* K) (W : Submodule K (Fin r → K)) :
    semiImage (levi r K A) σ (W.map (xEmb r K)) =
      ((LinearFlag.coordImage σ W).map (mulVecLin (A : Matrix (Fin r) (Fin r) K))).map
        (xEmb r K) := by
  rw [semiImage, sCoordImage_map_xEmb, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun x => levi_xEmb A x

end XEmb

section Opposite

theorem flag_top_inf_ySpan : flag r K r ⊓ ySpan r K = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, mem_flag_top_iff, mem_ySpan_iff] at hv
  rw [Submodule.mem_bot]
  funext c
  rcases c with i | i
  · exact hv.2 i
  · exact hv.1 i

theorem isMaxSing_flag_top : IsMaxSing (quadPlus r K) (flag r K r) := by
  rw [flag_eq_coordSpan]
  refine isMaxSing_coordSpan fun x => ?_
  rcases x with i | i <;> simp

theorem isMaxSing_ySpan : IsMaxSing (quadPlus r K) (ySpan r K) := by
  refine isMaxSing_coordSpan fun x => ?_
  rcases x with i | i <;> simp

theorem finrank_ySpan : finrank K (ySpan r K) = r :=
  (orthogonal_geometry_split_Witt_flags (nondegenerate_polarBilin_quadPlus r K) finrank_split
    ⟨flag r K r, finrank_flag le_rfl, fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩).2 _
    isMaxSing_ySpan.1 isMaxSing_ySpan.2

theorem exists_radical_map_ySpan_eq {Y' : Submodule K (Fin r ⊕ Fin r → K)}
    (hYs : ∀ v ∈ Y', quadPlus r K v = 0) (hYd : finrank K Y' = r)
    (hXY : flag r K r ⊓ Y' = ⊥) :
    ∃ C : Matrix (Fin r) (Fin r) K, C ∈ altSubgroup r K ∧
      (ySpan r K).map ((radical r K (Multiplicative.ofAdd C) :
        (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) : (Fin r ⊕ Fin r → K) →ₗ[K] _) = Y' := by
  set p : Y' →ₗ[K] (Fin r → K) := (LinearMap.funLeft K K Sum.inr).comp Y'.subtype with hp
  have hinj : Function.Injective p := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have hvX : (v : Fin r ⊕ Fin r → K) ∈ flag r K r :=
      mem_flag_top_iff.2 fun i => congrFun hv i
    have : (v : Fin r ⊕ Fin r → K) ∈ flag r K r ⊓ Y' := ⟨hvX, v.2⟩
    rw [hXY, Submodule.mem_bot] at this
    exact (Submodule.mem_bot K).2 (Subtype.ext this)
  have hsurj : Function.Surjective p := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj
    rw [hYd, Module.finrank_fin_fun]
  set e := LinearEquiv.ofBijective p ⟨hinj, hsurj⟩ with he
  set D : (Fin r → K) →ₗ[K] (Fin r → K) :=
    (LinearMap.funLeft K K Sum.inl).comp (Y'.subtype.comp e.symm.toLinearMap) with hD
  set C := LinearMap.toMatrix' D with hC
  have hw : ∀ y : Fin r → K, ((e.symm y : Y') : Fin r ⊕ Fin r → K) = Sum.elim (C *ᵥ y) y := by
    intro y
    funext c
    rcases c with i | i
    · rw [hC, LinearMap.toMatrix'_mulVec]
      rfl
    · have := congrFun (e.apply_symm_apply y) i
      exact this
  have hCalt : C ∈ altSubgroup r K := by
    refine alternating_of_mulVec_dotProduct_self fun y => ?_
    have h := hYs _ (e.symm y).2
    rw [hw, quadPlus_apply] at h
    exact h
  refine ⟨C, hCalt, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hv0 : (fun i => v (Sum.inl i)) = 0 := funext (mem_ySpan_iff.1 hv)
    have hrad : (radical r K (Multiplicative.ofAdd C) : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) v =
        Sum.elim (C *ᵥ (fun i => v (Sum.inr i))) (fun i => v (Sum.inr i)) := by
      rw [radical_eq_matrixEquiv, matrixEquiv_apply, coe_radicalGL, toAdd_ofAdd, blockUnip,
        fromBlocks_mulVec_apply]
      funext c
      rcases c with i | i <;> simp [Function.comp_def, hv0]
    change (radical r K (Multiplicative.ofAdd C) : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) v ∈ Y'
    rw [hrad, ← hw]
    exact (e.symm _).2
  · rw [LinearEquiv.finrank_map_eq, finrank_ySpan, hYd]

theorem polarImage_inf_eq_bot (φ : Points (quadPlus r K) ≃ Points (quadPlus r K))
    (hφ : ∀ L M : Points (quadPlus r K),
      PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K) (φ L).val (φ M).val) :
    polarImage r K φ (flag r K r) ⊓ polarImage r K φ (ySpan r K) = ⊥ := by
  have hX := totSing_polarImage φ hφ isMaxSing_flag_top.1
  have hY := totSing_polarImage φ hφ isMaxSing_ySpan.1
  set Z := polarImage r K φ (flag r K r) ⊓ polarImage r K φ (ySpan r K) with hZ
  have hZs : ∀ v ∈ Z, quadPlus r K v = 0 := fun v hv => hX v hv.1
  have hφ' := polarOrtho_symm_iff φ hφ
  have h1 : polarImage r K φ.symm Z ≤ flag r K r := by
    rw [← polarImage_symm_polarImage φ hφ isMaxSing_flag_top.1]
    exact (polarImage_le_iff φ.symm hφ' hZs hX).2 inf_le_left
  have h2 : polarImage r K φ.symm Z ≤ ySpan r K := by
    rw [← polarImage_symm_polarImage φ hφ isMaxSing_ySpan.1]
    exact (polarImage_le_iff φ.symm hφ' hZs hY).2 inf_le_right
  have h0 : polarImage r K φ.symm Z = ⊥ := by
    rw [eq_bot_iff, ← flag_top_inf_ySpan]
    exact le_inf h1 h2
  have hd := finrank_polarImage φ.symm hφ' hZs
  rw [h0, finrank_bot] at hd
  exact Submodule.finrank_eq_zero.1 hd.symm

end Opposite

section XPoint

@[expose] def xPoint (L' : ProjectiveGeometry.Point r K) : Points (quadPlus r K) :=
  ⟨L'.val.map (xEmb r K), by rw [finrank_map_xEmb]; exact L'.2,
    fun v hv => isMaxSing_flag_top.1 v (map_xEmb_le _ hv)⟩

theorem coe_xPoint (L' : ProjectiveGeometry.Point r K) :
    (xPoint L').val = L'.val.map (xEmb r K) :=
  rfl

@[expose] def toKPoint (L : Points (quadPlus r K)) (hL : L.val ≤ flag r K r) :
    ProjectiveGeometry.Point r K :=
  ⟨L.val.comap (xEmb r K), by rw [finrank_comap_xEmb hL]; exact L.2.1⟩

theorem coe_toKPoint (L : Points (quadPlus r K)) (hL : L.val ≤ flag r K r) :
    (toKPoint L hL).val = L.val.comap (xEmb r K) :=
  rfl

theorem xPoint_toKPoint (L : Points (quadPlus r K)) (hL : L.val ≤ flag r K r) :
    xPoint (toKPoint L hL) = L :=
  Subtype.ext (map_comap_xEmb hL)

theorem comap_le_comap_xEmb_iff {W W' : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : W ≤ flag r K r) (hW' : W' ≤ flag r K r) :
    W.comap (xEmb r K) ≤ W'.comap (xEmb r K) ↔ W ≤ W' := by
  rw [← Submodule.map_le_map_iff_of_injective xEmb_injective, map_comap_xEmb hW,
    map_comap_xEmb hW']

end XPoint

theorem eq_of_mem_ySpan (ψ : Points (quadPlus r K) ≃ Points (quadPlus r K))
    (hψ : ∀ L M : Points (quadPlus r K),
      PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K) (ψ L).val (ψ M).val)
    (hX : ∀ L : Points (quadPlus r K), L.val ≤ flag r K r → ψ L = L)
    {L : Points (quadPlus r K)} (hL : L.val ≤ ySpan r K) (hψL : (ψ L).val ≤ ySpan r K) :
    ψ L = L := by
  obtain ⟨w, hw0, hw⟩ := exists_eq_span_of_points L
  obtain ⟨w', hw'0, hw'⟩ := exists_eq_span_of_points (ψ L)
  have hwY : w ∈ ySpan r K := hL (by rw [hw]; exact mem_span_singleton_self w)
  have hw'Y : w' ∈ ySpan r K := hψL (by rw [hw']; exact mem_span_singleton_self w')
  have hkey : ∀ u : Fin r → K, u ⬝ᵥ (fun i => w (Sum.inr i)) = 0 ↔
      u ⬝ᵥ (fun i => w' (Sum.inr i)) = 0 := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    have hu0 : (Sum.elim u 0 : Fin r ⊕ Fin r → K) ≠ 0 := fun h => hu (funext fun i => by
      simpa using congrFun h (Sum.inl i))
    have huQ : quadPlus r K (Sum.elim u 0) = 0 := by simp [quadPlus_apply]
    have hfix := hX (spanPoint hu0 huQ) ((span_singleton_le_iff_mem _ _).2
      (mem_flag_top_iff.2 fun i => rfl))
    have h := hψ L (spanPoint hu0 huQ)
    rw [hfix, hw', hw] at h
    change PolarOrtho _ (K ∙ w) (K ∙ _) ↔ PolarOrtho _ (K ∙ w') (K ∙ _) at h
    rw [polarOrtho_span_singleton, polarOrtho_span_singleton, polar_inl_left,
      polar_inl_left] at h
    exact h
  have hy0 : (fun i => w (Sum.inr i)) ≠ 0 := by
    intro h
    apply hw0
    funext c
    rcases c with i | i
    · exact mem_ySpan_iff.1 hwY i
    · exact congrFun h i
  obtain ⟨l, hl, hly⟩ := exists_smul_eq_of_dotProduct_iff hy0 hkey
  have hww : w' = l • w := by
    funext c
    rcases c with i | i
    · rw [mem_ySpan_iff.1 hw'Y i, Pi.smul_apply, mem_ySpan_iff.1 hwY i, smul_zero]
    · exact congrFun hly i
  apply Subtype.ext
  rw [hw', hw, hww, span_singleton_smul_eq (IsUnit.mk0 _ hl)]


theorem orthogonal_geometry_split_opposite_normalization {K : Type*} [Field K] {r : ℕ}
    (hr : 3 ≤ r) (φ : Points (quadPlus r K) ≃ Points (quadPlus r K))
    (hφ : ∀ L M : Points (quadPlus r K),
      PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K) (φ L).val (φ M).val) :
    ∃ (σ : K ≃+* K) (A : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)),
      A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) ∧
      (∀ v, quadPlus r K (A (sCoord σ v)) = σ (quadPlus r K v)) ∧
      ∀ L : Points (quadPlus r K), (L.val ≤ flag r K r ∨ L.val ≤ ySpan r K) →
        (φ L).val = semiImage A σ L.val := by
  have hXs := isMaxSing_flag_top (r := r) (K := K)
  have hYs := isMaxSing_ySpan (r := r) (K := K)
  have hX₁s := totSing_polarImage φ hφ hXs.1
  have hY₁s := totSing_polarImage φ hφ hYs.1
  have hX₁d : finrank K (polarImage r K φ (flag r K r)) = r := by
    rw [finrank_polarImage φ hφ hXs.1, finrank_flag le_rfl]
  have hY₁d : finrank K (polarImage r K φ (ySpan r K)) = r := by
    rw [finrank_polarImage φ hφ hYs.1, finrank_ySpan]
  have hXY₁ := polarImage_inf_eq_bot φ hφ
  obtain ⟨g, hg, hgX⟩ := exists_isometry_map_eq (r := r) (K := K) le_rfl ⟨hX₁d, hX₁s⟩
  have hginv : g.symm ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := inv_mem hg
  set Y' := (polarImage r K φ (ySpan r K)).map
    (g.symm : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) with hY'
  have hY's : ∀ v ∈ Y', quadPlus r K v = 0 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [LinearEquiv.coe_coe, map_of_mem hginv]
    exact hY₁s v hv
  have hY'd : finrank K Y' = r := by rw [hY', LinearEquiv.finrank_map_eq, hY₁d]
  have hXY' : flag r K r ⊓ Y' = ⊥ := by
    have hX' : flag r K r = (polarImage r K φ (flag r K r)).map
        (g.symm : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) := by
      rw [← hgX, map_symm_map]
    rw [hX', hY', ← Submodule.map_inf _ g.symm.injective, hXY₁, Submodule.map_bot]
  obtain ⟨C, hC, hCY⟩ := exists_radical_map_ySpan_eq hY's hY'd hXY'
  set u := radical r K (Multiplicative.ofAdd C) with hu
  have huB := posUnip_le_posBorel (radical_mem_posUnip hC)
  have huO : u ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) :=
    posBorel_le_orthogonalGroup huB
  have huX : (flag r K r).map (u : (Fin r ⊕ Fin r → K) →ₗ[K] _) = flag r K r :=
    (mem_posBorel.1 huB).2 r
  set T₀ := g * u with hT₀def
  have hT₀ : T₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := mul_mem hg huO
  have hT₀X : (flag r K r).map (T₀ : (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      polarImage r K φ (flag r K r) := by
    rw [hT₀def, LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp, huX,
      hgX]
  have hT₀Y : (ySpan r K).map (T₀ : (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      polarImage r K φ (ySpan r K) := by
    rw [hT₀def, LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp, hCY,
      hY', map_map_symm]
  set φ₁ := φ.trans (semiPointEquiv (RingEquiv.refl K) hT₀).symm with hφ₁def
  have hφ₁ := polarOrtho_trans_symm (RingEquiv.refl K) hT₀ φ hφ
  have hpre0 : ∀ W, semiPreimage T₀ (RingEquiv.refl K) W =
      W.map (T₀.symm : (Fin r ⊕ Fin r → K) →ₗ[K] _) := fun W => by
    ext v
    rfl
  have hφ₁X : polarImage r K φ₁ (flag r K r) = flag r K r := by
    rw [hφ₁def, polarImage_trans_symm _ hT₀ φ hφ hXs.1, hpre0, ← hT₀X, map_symm_map]
  have hφ₁Y : polarImage r K φ₁ (ySpan r K) = ySpan r K := by
    rw [hφ₁def, polarImage_trans_symm _ hT₀ φ hφ hYs.1, hpre0, ← hT₀Y, map_symm_map]
  have hptsX : ptsIn (quadPlus r K) (flag r K r) = φ₁ '' ptsIn (quadPlus r K) (flag r K r) := by
    rw [← ptsIn_polarImage φ₁ hφ₁ hXs.1, hφ₁X]
  have hptsY : ptsIn (quadPlus r K) (ySpan r K) = φ₁ '' ptsIn (quadPlus r K) (ySpan r K) := by
    rw [← ptsIn_polarImage φ₁ hφ₁ hYs.1, hφ₁Y]
  have hmapX : ∀ L : Points (quadPlus r K), L.val ≤ flag r K r → (φ₁ L).val ≤ flag r K r :=
    fun L hL => by
      have : φ₁ L ∈ φ₁ '' ptsIn (quadPlus r K) (flag r K r) := ⟨L, hL, rfl⟩
      rw [← hptsX] at this
      exact this
  have hmapY : ∀ L : Points (quadPlus r K), L.val ≤ ySpan r K → (φ₁ L).val ≤ ySpan r K :=
    fun L hL => by
      have : φ₁ L ∈ φ₁ '' ptsIn (quadPlus r K) (ySpan r K) := ⟨L, hL, rfl⟩
      rw [← hptsY] at this
      exact this
  have hmapX' : ∀ L : Points (quadPlus r K), L.val ≤ flag r K r →
      (φ₁.symm L).val ≤ flag r K r := fun L hL => by
    have : L ∈ ptsIn (quadPlus r K) (flag r K r) := hL
    rw [hptsX] at this
    obtain ⟨M, hM, rfl⟩ := this
    rwa [Equiv.symm_apply_apply]
  have hfwd : ∀ L' : ProjectiveGeometry.Point r K, (φ₁ (xPoint L')).val ≤ flag r K r :=
    fun L' => hmapX _ (map_xEmb_le _)
  have hbwd : ∀ L' : ProjectiveGeometry.Point r K, (φ₁.symm (xPoint L')).val ≤ flag r K r :=
    fun L' => hmapX' _ (map_xEmb_le _)
  let f : ProjectiveGeometry.Point r K ≃ ProjectiveGeometry.Point r K :=
    { toFun := fun L' => toKPoint (φ₁ (xPoint L')) (hfwd L')
      invFun := fun L' => toKPoint (φ₁.symm (xPoint L')) (hbwd L')
      left_inv := fun L' => Subtype.ext (by
        rw [coe_toKPoint, xPoint_toKPoint, Equiv.symm_apply_apply, coe_xPoint, comap_map_xEmb])
      right_inv := fun L' => Subtype.ext (by
        rw [coe_toKPoint, xPoint_toKPoint, Equiv.apply_symm_apply, coe_xPoint, comap_map_xEmb]) }
  have hHs : ∀ H : Submodule K (Fin r → K), ∀ v ∈ H.map (xEmb r K), quadPlus r K v = 0 :=
    fun H v hv => hXs.1 v (map_xEmb_le H hv)
  have hφ₁' := polarOrtho_symm_iff φ₁ hφ₁
  have hle₁ : ∀ H : Submodule K (Fin r → K),
      polarImage r K φ₁ (H.map (xEmb r K)) ≤ flag r K r := fun H => by
    rw [← hφ₁X]
    exact (polarImage_le_iff φ₁ hφ₁ (hHs H) hXs.1).2 (map_xEmb_le H)
  have hφ₁sX : polarImage r K φ₁.symm (flag r K r) = flag r K r := by
    conv_lhs => rw [← hφ₁X]
    exact polarImage_symm_polarImage φ₁ hφ₁ hXs.1
  have hle₂ : ∀ H : Submodule K (Fin r → K),
      polarImage r K φ₁.symm (H.map (xEmb r K)) ≤ flag r K r := fun H => by
    rw [← hφ₁sX]
    exact (polarImage_le_iff φ₁.symm hφ₁' (hHs H) hXs.1).2 (map_xEmb_le H)
  let hyp : ProjectiveGeometry.Hyperplane r K ≃ ProjectiveGeometry.Hyperplane r K :=
    { toFun := fun H => ⟨(polarImage r K φ₁ (H.val.map (xEmb r K))).comap (xEmb r K), by
        rw [finrank_comap_xEmb (hle₁ H.val), finrank_polarImage φ₁ hφ₁ (hHs H.val),
          finrank_map_xEmb]
        exact H.2⟩
      invFun := fun H => ⟨(polarImage r K φ₁.symm (H.val.map (xEmb r K))).comap (xEmb r K), by
        rw [finrank_comap_xEmb (hle₂ H.val), finrank_polarImage φ₁.symm hφ₁' (hHs H.val),
          finrank_map_xEmb]
        exact H.2⟩
      left_inv := fun H => Subtype.ext (by
        change (polarImage r K φ₁.symm (((polarImage r K φ₁ (H.val.map (xEmb r K))).comap
          (xEmb r K)).map (xEmb r K))).comap (xEmb r K) = H.val
        rw [map_comap_xEmb (hle₁ H.val), polarImage_symm_polarImage φ₁ hφ₁ (hHs H.val),
          comap_map_xEmb])
      right_inv := fun H => Subtype.ext (by
        change (polarImage r K φ₁ (((polarImage r K φ₁.symm (H.val.map (xEmb r K))).comap
          (xEmb r K)).map (xEmb r K))).comap (xEmb r K) = H.val
        have h := polarImage_symm_polarImage φ₁.symm hφ₁' (hHs H.val)
        rw [Equiv.symm_symm] at h
        rw [map_comap_xEmb (hle₂ H.val), h, comap_map_xEmb]) }
  have hinc : ∀ (L' : ProjectiveGeometry.Point r K) (H : ProjectiveGeometry.Hyperplane r K),
      (L' : Submodule K (Fin r → K)) ≤ H ↔
        (f L' : Submodule K (Fin r → K)) ≤ hyp H := by
    intro L' H
    change L'.val ≤ H.val ↔ (φ₁ (xPoint L')).val.comap (xEmb r K) ≤
      (polarImage r K φ₁ (H.val.map (xEmb r K))).comap (xEmb r K)
    rw [comap_le_comap_xEmb_iff (hfwd L') (hle₁ H.val), ← polarImage_point φ₁ (xPoint L'),
      polarImage_le_iff φ₁ hφ₁ (xPoint L').2.2 (hHs H.val), coe_xPoint,
      Submodule.map_le_map_iff_of_injective xEmb_injective]
  obtain ⟨A₀, σ, hfA, -⟩ := ProjectiveGeometry.semilinear_realization hr f hyp hinc
  have hT₁ := levi_mem_orthogonalGroup (r := r) (K := K) A₀
  have hφ₁T₁ : ∀ L : Points (quadPlus r K), L.val ≤ flag r K r →
      (φ₁ L).val = semiImage (levi r K A₀) σ L.val := by
    intro L hL
    have hLL := xPoint_toKPoint L hL
    have h1 := hfA (toKPoint L hL)
    change (φ₁ (xPoint (toKPoint L hL))).val.comap (xEmb r K) = _ at h1
    rw [hLL] at h1
    rw [← map_comap_xEmb (hmapX L hL), h1, ← semiImage_map_xEmb, ← coe_xPoint, hLL]
  set φ₂ := φ₁.trans (semiPointEquiv σ hT₁).symm with hφ₂def
  have hφ₂ := polarOrtho_trans_symm σ hT₁ φ₁ hφ₁
  have hφ₂X : ∀ L : Points (quadPlus r K), L.val ≤ flag r K r → φ₂ L = L := by
    intro L hL
    apply Subtype.ext
    rw [hφ₂def, Equiv.trans_apply, coe_semiPointEquiv_symm, hφ₁T₁ L hL, semiPreimage_semiImage]
  have hpreY : ∀ v, v ∈ semiPreimage (levi r K A₀) σ (ySpan r K) → v ∈ ySpan r K := by
    intro v hv
    rw [semiPreimage, mem_sCoordImage, RingEquiv.symm_symm, Submodule.mem_map_equiv,
      LinearEquiv.symm_symm] at hv
    have h1 : sCoord σ v ∈ ySpan r K := by
      have := levi_mem_ySpan A₀⁻¹ hv
      rwa [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at this
    rw [mem_ySpan_iff] at h1 ⊢
    intro i
    exact (map_eq_zero_iff σ σ.injective).1 (h1 i)
  have hφ₂Y : ∀ L : Points (quadPlus r K), L.val ≤ ySpan r K → φ₂ L = L := by
    intro L hL
    refine eq_of_mem_ySpan φ₂ hφ₂ hφ₂X hL ?_
    rw [hφ₂def, Equiv.trans_apply, coe_semiPointEquiv_symm]
    exact fun v hv => hpreY v (semiPreimage_mono _ σ (hmapY L hL) hv)
  have hA := mul_mem hT₀ hT₁
  refine ⟨σ, T₀ * levi r K A₀, hA, quadPlus_semi σ hA, fun L hL => ?_⟩
  have hfix : φ₂ L = L := hL.elim (hφ₂X L) (hφ₂Y L)
  have h1 : (φ₁ L).val = semiImage (levi r K A₀) σ L.val := by
    have := congrArg (fun M : Points (quadPlus r K) => semiImage (levi r K A₀) σ M.val) hfix
    simp only [hφ₂def, Equiv.trans_apply, coe_semiPointEquiv_symm, semiImage_semiPreimage]
      at this
    exact this
  have h2 : (φ L).val = (φ₁ L).val.map (T₀ : (Fin r ⊕ Fin r → K) →ₗ[K] _) := by
    rw [hφ₁def, Equiv.trans_apply, coe_semiPointEquiv_symm, hpre0, map_map_symm]
  rw [h2, h1, semiImage, semiImage, ← Submodule.map_comp]
  rfl

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

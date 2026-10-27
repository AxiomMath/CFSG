module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryOpposite
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailMixedCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSemiSim

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module
  Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
  (Points pointMk pointMk_submodule exists_eq_pointMk)

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}

section XEmb

@[expose] def xEmbT (r : ℕ) (K : Type*) [Field K] (A : Type*) [AddCommGroup A] [Module K A] :
    (Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) × A :=
  (LinearMap.inl K (Fin r ⊕ Fin r → K) A).comp (xEmb r K)

theorem xEmbT_apply (x : Fin r → K) : xEmbT r K A x = (Sum.elim x 0, 0) :=
  rfl

theorem xEmbT_injective : Function.Injective (xEmbT r K A) := fun _ _ h =>
  xEmb_injective (congrArg Prod.fst h)

theorem xEmbT_mem (x : Fin r → K) : xEmbT r K A x ∈ (flag r K r).prod ⊥ :=
  Submodule.mem_prod.2 ⟨mem_flag_top_iff.2 fun _ => rfl, Submodule.zero_mem _⟩

theorem range_xEmbT : LinearMap.range (xEmbT r K A) = (flag r K r).prod ⊥ := by
  rw [xEmbT, LinearMap.range_comp, range_xEmb, Submodule.map_inl]

theorem map_comap_xEmbT {W : Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hW : W ≤ (flag r K r).prod ⊥) : (W.comap (xEmbT r K A)).map (xEmbT r K A) = W := by
  rw [Submodule.map_comap_eq, range_xEmbT, inf_eq_right.2 hW]

theorem comap_map_xEmbT (W : Submodule K (Fin r → K)) :
    (W.map (xEmbT r K A)).comap (xEmbT r K A) = W :=
  Submodule.comap_map_eq_of_injective xEmbT_injective W

theorem finrank_map_xEmbT (W : Submodule K (Fin r → K)) :
    finrank K (W.map (xEmbT r K A)) = finrank K W :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ xEmbT_injective W)).symm

theorem finrank_comap_xEmbT {W : Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hW : W ≤ (flag r K r).prod ⊥) : finrank K (W.comap (xEmbT r K A)) = finrank K W := by
  rw [← finrank_map_xEmbT (A := A), map_comap_xEmbT hW]

theorem map_xEmbT_le (W : Submodule K (Fin r → K)) :
    W.map (xEmbT r K A) ≤ (flag r K r).prod ⊥ := by
  rw [← range_xEmbT]
  exact LinearMap.map_le_range

theorem comap_le_comap_xEmbT_iff {W W' : Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hW : W ≤ (flag r K r).prod ⊥) (hW' : W' ≤ (flag r K r).prod ⊥) :
    W.comap (xEmbT r K A) ≤ W'.comap (xEmbT r K A) ↔ W ≤ W' := by
  rw [← Submodule.map_le_map_iff_of_injective (xEmbT_injective (A := A)), map_comap_xEmbT hW,
    map_comap_xEmbT hW']

variable (q : QuadraticForm K A)

@[expose] def xPointT (L' : ProjectiveGeometry.Point r K) : Points (quadTail r q) :=
  ⟨L'.val.map (xEmbT r K A), by rw [finrank_map_xEmbT]; exact L'.2,
    fun _ hv => quadTail_eq_zero_of_mem_xSpan (map_xEmbT_le _ hv)⟩

theorem coe_xPointT (L' : ProjectiveGeometry.Point r K) :
    (xPointT q L').val = L'.val.map (xEmbT r K A) :=
  rfl

variable {q}

@[expose] def toKPointT (L : Points (quadTail r q)) (hL : L.val ≤ (flag r K r).prod ⊥) :
    ProjectiveGeometry.Point r K :=
  ⟨L.val.comap (xEmbT r K A), by rw [finrank_comap_xEmbT hL]; exact L.2.1⟩

theorem coe_toKPointT (L : Points (quadTail r q)) (hL : L.val ≤ (flag r K r).prod ⊥) :
    (toKPointT L hL).val = L.val.comap (xEmbT r K A) :=
  rfl

theorem xPointT_toKPointT (L : Points (quadTail r q)) (hL : L.val ≤ (flag r K r).prod ⊥) :
    xPointT q (toKPointT L hL) = L :=
  Subtype.ext (map_comap_xEmbT hL)

end XEmb

section Projective

variable [FiniteDimensional K A] {q q' : QuadraticForm K A}

theorem exists_semilinear_on_xSpan (hr : 3 ≤ r) (h₁ : IsInfOfMax (quadTail r q))
    (h₂ : IsInfOfMax (quadTail r q')) (φ : Points (quadTail r q) ≃ Points (quadTail r q'))
    (hφ : ∀ L M : Points (quadTail r q),
      PolarOrtho (quadTail r q) L.val M.val ↔ PolarOrtho (quadTail r q') (φ L).val (φ M).val)
    (hφX : polarImage₂ φ ((flag r K r).prod ⊥) = (flag r K r).prod ⊥) :
    ∃ (C : GL (Fin r) K) (σ : K ≃+* K), ∀ (x : Fin r → K) (hx0 : xEmbT r K A x ≠ 0)
      (hxQ : quadTail r q (xEmbT r K A x) = 0),
      (φ (pointMk (xEmbT r K A x) hx0 hxQ)).val =
        K ∙ xEmbT r K A ((C : Matrix (Fin r) (Fin r) K) *ᵥ fun i => σ (x i)) := by
  have hXs : ∀ v ∈ (flag r K r).prod (⊥ : Submodule K A), quadTail r q v = 0 :=
    fun _ hv => quadTail_eq_zero_of_mem_xSpan hv
  have hXs' : ∀ v ∈ (flag r K r).prod (⊥ : Submodule K A), quadTail r q' v = 0 :=
    fun _ hv => quadTail_eq_zero_of_mem_xSpan hv
  have hφ' := polarOrtho_symm_iff₂ φ hφ
  have hpts : ptsIn (quadTail r q') ((flag r K r).prod ⊥) =
      φ '' ptsIn (quadTail r q) ((flag r K r).prod ⊥) := by
    rw [← ptsIn_polarImage₂ φ hφ h₁ hXs, hφX]
  have hfwd : ∀ L' : ProjectiveGeometry.Point r K,
      (φ (xPointT q L')).val ≤ (flag r K r).prod ⊥ := fun L' => by
    have : φ (xPointT q L') ∈ φ '' ptsIn (quadTail r q) ((flag r K r).prod ⊥) :=
      ⟨_, map_xEmbT_le _, rfl⟩
    rw [← hpts] at this
    exact this
  have hbwd : ∀ L' : ProjectiveGeometry.Point r K,
      (φ.symm (xPointT q' L')).val ≤ (flag r K r).prod ⊥ := fun L' => by
    have : xPointT q' L' ∈ ptsIn (quadTail r q') ((flag r K r).prod ⊥) := map_xEmbT_le _
    rw [hpts] at this
    obtain ⟨M, hM, hMe⟩ := this
    rw [← hMe, Equiv.symm_apply_apply]
    exact hM
  let f : ProjectiveGeometry.Point r K ≃ ProjectiveGeometry.Point r K :=
    { toFun := fun L' => toKPointT (φ (xPointT q L')) (hfwd L')
      invFun := fun L' => toKPointT (φ.symm (xPointT q' L')) (hbwd L')
      left_inv := fun L' => Subtype.ext (by
        rw [coe_toKPointT, xPointT_toKPointT, Equiv.symm_apply_apply, coe_xPointT,
          comap_map_xEmbT])
      right_inv := fun L' => Subtype.ext (by
        rw [coe_toKPointT, xPointT_toKPointT, Equiv.apply_symm_apply, coe_xPointT,
          comap_map_xEmbT]) }
  have hHs : ∀ H : Submodule K (Fin r → K), ∀ v ∈ H.map (xEmbT r K A), quadTail r q v = 0 :=
    fun H v hv => hXs v (map_xEmbT_le H hv)
  have hHs' : ∀ H : Submodule K (Fin r → K), ∀ v ∈ H.map (xEmbT r K A), quadTail r q' v = 0 :=
    fun H v hv => hXs' v (map_xEmbT_le H hv)
  have hle₁ : ∀ H : Submodule K (Fin r → K),
      polarImage₂ φ (H.map (xEmbT r K A)) ≤ (flag r K r).prod ⊥ := fun H => by
    rw [← hφX]
    exact (polarImage₂_le_iff φ hφ h₁ (hHs H) hXs).2 (map_xEmbT_le H)
  have hφsX : polarImage₂ φ.symm ((flag r K r).prod ⊥) = (flag r K r).prod ⊥ := by
    conv_lhs => rw [← hφX]
    exact polarImage₂_symm_polarImage₂ φ hφ h₁ hXs
  have hle₂ : ∀ H : Submodule K (Fin r → K),
      polarImage₂ φ.symm (H.map (xEmbT r K A)) ≤ (flag r K r).prod ⊥ := fun H => by
    rw [← hφsX]
    exact (polarImage₂_le_iff φ.symm hφ' h₂ (hHs' H) hXs').2 (map_xEmbT_le H)
  let hyp : ProjectiveGeometry.Hyperplane r K ≃ ProjectiveGeometry.Hyperplane r K :=
    { toFun := fun H => ⟨(polarImage₂ φ (H.val.map (xEmbT r K A))).comap (xEmbT r K A), by
        rw [finrank_comap_xEmbT (hle₁ H.val), finrank_polarImage₂ φ hφ h₁ h₂ (hHs H.val),
          finrank_map_xEmbT]
        exact H.2⟩
      invFun := fun H => ⟨(polarImage₂ φ.symm (H.val.map (xEmbT r K A))).comap (xEmbT r K A), by
        rw [finrank_comap_xEmbT (hle₂ H.val), finrank_polarImage₂ φ.symm hφ' h₂ h₁ (hHs' H.val),
          finrank_map_xEmbT]
        exact H.2⟩
      left_inv := fun H => Subtype.ext (by
        change (polarImage₂ φ.symm (((polarImage₂ φ (H.val.map (xEmbT r K A))).comap
          (xEmbT r K A)).map (xEmbT r K A))).comap (xEmbT r K A) = H.val
        rw [map_comap_xEmbT (hle₁ H.val), polarImage₂_symm_polarImage₂ φ hφ h₁ (hHs H.val),
          comap_map_xEmbT])
      right_inv := fun H => Subtype.ext (by
        change (polarImage₂ φ (((polarImage₂ φ.symm (H.val.map (xEmbT r K A))).comap
          (xEmbT r K A)).map (xEmbT r K A))).comap (xEmbT r K A) = H.val
        have h := polarImage₂_symm_polarImage₂ φ.symm hφ' h₂ (hHs' H.val)
        rw [Equiv.symm_symm] at h
        rw [map_comap_xEmbT (hle₂ H.val), h, comap_map_xEmbT]) }
  have hinc : ∀ (L' : ProjectiveGeometry.Point r K) (H : ProjectiveGeometry.Hyperplane r K),
      (L' : Submodule K (Fin r → K)) ≤ H ↔ (f L' : Submodule K (Fin r → K)) ≤ hyp H := by
    intro L' H
    change L'.val ≤ H.val ↔ (φ (xPointT q L')).val.comap (xEmbT r K A) ≤
      (polarImage₂ φ (H.val.map (xEmbT r K A))).comap (xEmbT r K A)
    rw [comap_le_comap_xEmbT_iff (hfwd L') (hle₁ H.val), ← polarImage₂_point φ (xPointT q L'),
      polarImage₂_le_iff φ hφ h₁ (xPointT q L').2.2 (hHs H.val), coe_xPointT,
      Submodule.map_le_map_iff_of_injective xEmbT_injective]
  obtain ⟨C, σ, hfA, -⟩ := ProjectiveGeometry.semilinear_realization hr f hyp hinc
  refine ⟨C, σ, fun x hx0 hxQ => ?_⟩
  have hx : x ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  obtain ⟨L', hL'⟩ : ∃ L' : ProjectiveGeometry.Point r K, L'.val = K ∙ x :=
    ⟨⟨K ∙ x, finrank_span_singleton hx⟩, rfl⟩
  have hpt : pointMk (Q := quadTail r q) (xEmbT r K A x) hx0 hxQ = xPointT q L' :=
    Subtype.ext (by rw [pointMk_submodule, coe_xPointT, hL', Submodule.map_span,
      Set.image_singleton])
  have h1 := hfA L'
  change (φ (xPointT q L')).val.comap (xEmbT r K A) = _ at h1
  rw [hpt, ← map_comap_xEmbT (hfwd L'), h1, hL', ProjectiveGeometry.coordImage_span_singleton,
    Submodule.map_span, Set.image_singleton, Submodule.map_span, Set.image_singleton,
    mulVecLin_apply]

end Projective

theorem eq_of_le_ySpan_tail {q q' : QuadraticForm K A}
    (ψ : Points (quadTail r q) ≃ Points (quadTail r q'))
    (hψ : ∀ L M : Points (quadTail r q),
      PolarOrtho (quadTail r q) L.val M.val ↔ PolarOrtho (quadTail r q') (ψ L).val (ψ M).val)
    (hX : ∀ L : Points (quadTail r q), L.val ≤ (flag r K r).prod ⊥ → (ψ L).val = L.val)
    {L : Points (quadTail r q)} (hL : L.val ≤ (ySpan r K).prod ⊥)
    (hψL : (ψ L).val ≤ (ySpan r K).prod ⊥) : (ψ L).val = L.val := by
  obtain ⟨w, hw0, hwQ, rfl⟩ := exists_eq_pointMk L
  obtain ⟨w', hw'0, hw'Q, hw'⟩ := exists_eq_pointMk (ψ (pointMk w hw0 hwQ))
  have hw'v : (ψ (pointMk w hw0 hwQ)).val = K ∙ w' := by rw [hw', pointMk_submodule]
  rw [pointMk_submodule] at hL
  rw [hw'v] at hψL
  rw [hw'v, pointMk_submodule]
  have hwY := Submodule.mem_prod.1 ((span_singleton_le_iff_mem _ _).1 hL)
  have hw'Y := Submodule.mem_prod.1 ((span_singleton_le_iff_mem _ _).1 hψL)
  have hkey : ∀ u : Fin r → K, u ⬝ᵥ (fun i => w.1 (Sum.inr i)) = 0 ↔
      u ⬝ᵥ (fun i => w'.1 (Sum.inr i)) = 0 := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    have hu0 : xEmbT r K A u ≠ 0 := fun h => hu (xEmbT_injective (h.trans (map_zero _).symm))
    have huQ : quadTail r q (xEmbT r K A u) = 0 := quadTail_eq_zero_of_mem_xSpan (xEmbT_mem u)
    have hfix := hX (pointMk _ hu0 huQ) (by
      rw [pointMk_submodule, span_singleton_le_iff_mem]
      exact xEmbT_mem u)
    have h := hψ (pointMk w hw0 hwQ) (pointMk _ hu0 huQ)
    rw [hfix, hw'v, pointMk_submodule, pointMk_submodule, polarOrtho_span_singleton_iff_polar,
      polarOrtho_span_singleton_iff_polar, polar_quadTail, polar_quadTail, xEmbT_apply] at h
    dsimp only at h
    simp only [polar_zero_right, add_zero, polar_inl_left] at h
    exact h
  have hy0 : (fun i => w.1 (Sum.inr i)) ≠ 0 := by
    intro h
    apply hw0
    refine Prod.ext (funext fun c => ?_) ((mem_bot K).1 hwY.2)
    rcases c with i | i
    · exact mem_ySpan_iff.1 hwY.1 i
    · exact congrFun h i
  obtain ⟨l, hl, hly⟩ := exists_smul_eq_of_dotProduct_iff hy0 hkey
  have hww : w' = l • w := by
    refine Prod.ext (funext fun c => ?_) ?_
    · rcases c with i | i
      · rw [mem_ySpan_iff.1 hw'Y.1 i, Prod.smul_fst, Pi.smul_apply, mem_ySpan_iff.1 hwY.1 i,
          smul_zero]
      · exact congrFun hly i
    · rw [(mem_bot K).1 hw'Y.2, Prod.smul_snd, (mem_bot K).1 hwY.2, smul_zero]
  rw [hww, span_singleton_smul_eq (IsUnit.mk0 _ hl)]

section BasisCoord

variable [FiniteDimensional K A]

variable (A) in
@[expose] noncomputable def basisCoord (σ : K ≃+* K) : A ≃ A :=
  (Module.finBasis K A).equivFun.toEquiv.trans
    ((Equiv.piCongrRight fun _ => σ.toEquiv).trans (Module.finBasis K A).equivFun.toEquiv.symm)

theorem basisCoord_apply (σ : K ≃+* K) (a : A) :
    basisCoord A σ a =
      (Module.finBasis K A).equivFun.symm fun i => σ ((Module.finBasis K A).equivFun a i) :=
  rfl

theorem basisCoord_add (σ : K ≃+* K) (x y : A) :
    basisCoord A σ (x + y) = basisCoord A σ x + basisCoord A σ y := by
  rw [basisCoord_apply, basisCoord_apply, basisCoord_apply, ← map_add]
  congr 1
  funext i
  simp only [map_add, Pi.add_apply]

theorem basisCoord_smul (σ : K ≃+* K) (c : K) (x : A) :
    basisCoord A σ (c • x) = σ c • basisCoord A σ x := by
  rw [basisCoord_apply, basisCoord_apply, ← map_smul]
  congr 1
  funext i
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]

end BasisCoord

section Twist

variable {σ : K ≃+* K} {s : A ≃ A}

theorem s_zero_of_smul (hs_smul : ∀ (c : K) x, s (c • x) = σ c • s x) : s 0 = 0 := by
  have h := hs_smul 0 0
  rw [zero_smul] at h
  rw [h, map_zero σ, zero_smul]

theorem polar_twist (hs_add : ∀ x y, s (x + y) = s x + s y) (q : QuadraticForm K A) (x y : A) :
    polar (fun a => σ.symm (q (s a))) x y = σ.symm (polar q (s x) (s y)) := by
  simp only [QuadraticMap.polar, hs_add, map_sub]

@[expose] def twistForm (hs_add : ∀ x y, s (x + y) = s x + s y)
    (hs_smul : ∀ (c : K) x, s (c • x) = σ c • s x) (q : QuadraticForm K A) :
    QuadraticForm K A :=
  QuadraticMap.ofPolar (fun a => σ.symm (q (s a)))
    (fun c a => by
      simp only [hs_smul, QuadraticMap.map_smul, smul_eq_mul, map_mul,
        RingEquiv.symm_apply_apply])
    (fun x x' y => by
      rw [polar_twist hs_add, polar_twist hs_add, polar_twist hs_add, hs_add, polar_add_left,
        map_add])
    (fun c x y => by
      rw [polar_twist hs_add, polar_twist hs_add, hs_smul, polar_smul_left, smul_eq_mul,
        smul_eq_mul, map_mul, RingEquiv.symm_apply_apply])

variable (hs_add : ∀ x y, s (x + y) = s x + s y) (hs_smul : ∀ (c : K) x, s (c • x) = σ c • s x)

theorem twistForm_apply (q : QuadraticForm K A) (a : A) :
    twistForm hs_add hs_smul q a = σ.symm (q (s a)) :=
  rfl

theorem polar_twistForm (q : QuadraticForm K A) (x y : A) :
    polar (twistForm hs_add hs_smul q) x y = σ.symm (polar q (s x) (s y)) :=
  polar_twist hs_add q x y

theorem anisotropic_twistForm {q : QuadraticForm K A} (hani : q.Anisotropic) :
    (twistForm hs_add hs_smul q).Anisotropic := fun a ha => by
  rw [twistForm_apply, map_eq_zero_iff σ.symm σ.symm.injective] at ha
  exact s.injective ((hani _ ha).trans (s_zero_of_smul hs_smul).symm)

theorem nondegenerate_twistForm {q : QuadraticForm K A} (hreg : (polarBilin q).Nondegenerate) :
    (polarBilin (twistForm hs_add hs_smul q)).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun a ha => s.injective ?_
  rw [s_zero_of_smul hs_smul]
  refine eq_zero_of_polar_eq_zero hreg fun w => ?_
  have h := ha (s.symm w)
  rw [polar_twistForm, Equiv.apply_symm_apply, map_eq_zero_iff σ.symm σ.symm.injective] at h
  exact h

@[expose] noncomputable def twistSim (q : QuadraticForm K A) (C : GL (Fin r) K) :
    SemiSim (quadTail r (twistForm hs_add hs_smul q)) (quadTail r q) where
  e :=
    { toFun := fun v => (levi r K C (sCoord σ v.1), s v.2)
      invFun := fun v => (sCoord σ.symm ((levi r K C).symm v.1), s.symm v.2)
      left_inv := fun v => by
        simp only [LinearEquiv.symm_apply_apply, sCoord_symm_sCoord, Equiv.symm_apply_apply]
      right_inv := fun v => by
        simp only [sCoord_sCoord_symm, LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply] }
  σ := σ
  μ := 1
  μ_ne_zero := one_ne_zero
  map_add' x y := by
    simp only [Equiv.coe_fn_mk, Prod.fst_add, Prod.snd_add, sCoord_add, map_add, hs_add,
      Prod.mk_add_mk]
  map_smul' c x := by
    simp only [Equiv.coe_fn_mk, Prod.smul_fst, Prod.smul_snd, sCoord_smul, map_smul, hs_smul,
      Prod.smul_mk]
  map_quad' v := by
    simp only [Equiv.coe_fn_mk, quadTail_apply, quadPlus_semi σ (levi_mem_orthogonalGroup C),
      twistForm_apply, map_add, one_mul, RingEquiv.apply_symm_apply]

theorem twistSim_e (q : QuadraticForm K A) (C : GL (Fin r) K)
    (v : (Fin r ⊕ Fin r → K) × A) :
    (twistSim hs_add hs_smul q C).e v = (levi r K C (sCoord σ v.1), s v.2) :=
  rfl

theorem twistSim_xEmbT (q : QuadraticForm K A) (C : GL (Fin r) K) (x : Fin r → K) :
    (twistSim hs_add hs_smul q C).e (xEmbT r K A x) =
      xEmbT r K A ((C : Matrix (Fin r) (Fin r) K) *ᵥ fun i => σ (x i)) := by
  rw [twistSim_e, xEmbT_apply, xEmbT_apply]
  dsimp only
  rw [← xEmb_apply, sCoord_xEmb, levi_xEmb, xEmb_apply, s_zero_of_smul hs_smul]

theorem mem_ySpan_of_twistSim (q : QuadraticForm K A) (C : GL (Fin r) K)
    {v : (Fin r ⊕ Fin r → K) × A}
    (hv : (twistSim hs_add hs_smul q C).e v ∈ (ySpan r K).prod ⊥) :
    v ∈ (ySpan r K).prod ⊥ := by
  rw [twistSim_e, Submodule.mem_prod] at hv
  obtain ⟨h1, h2⟩ := hv
  dsimp only at h1 h2
  refine Submodule.mem_prod.2 ⟨?_, (mem_bot K).2 (s.injective ?_)⟩
  · have h := levi_mem_ySpan C⁻¹ h1
    rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h
    rw [mem_ySpan_iff] at h ⊢
    intro i
    exact (map_eq_zero_iff σ σ.injective).1 (h i)
  · rw [(mem_bot K).1 h2, s_zero_of_smul hs_smul]

end Twist

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

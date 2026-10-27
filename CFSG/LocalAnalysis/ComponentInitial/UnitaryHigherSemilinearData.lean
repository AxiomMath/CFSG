module

public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

section Coord

variable {K : Type} [Field K] {ι : Type}

@[expose] def coordImage (σ : K ≃+* K) (W : Submodule K (ι → K)) : Submodule K (ι → K) where
  carrier := {v | (fun a => σ.symm (v a)) ∈ W}
  add_mem' {v w} hv hw := by
    change (fun a => σ.symm ((v + w) a)) ∈ W
    convert W.add_mem hv hw using 1
    funext a
    simp
  zero_mem' := by
    change (fun a => σ.symm ((0 : ι → K) a)) ∈ W
    convert W.zero_mem using 1
    funext a
    simp
  smul_mem' c v hv := by
    change (fun a => σ.symm ((c • v) a)) ∈ W
    convert W.smul_mem (σ.symm c) hv using 1
    funext a
    simp

theorem mem_coordImage {σ : K ≃+* K} {W : Submodule K (ι → K)} {v : ι → K} :
    v ∈ coordImage σ W ↔ (fun a => σ.symm (v a)) ∈ W :=
  Iff.rfl

theorem coordImage_one (W : Submodule K (ι → K)) : coordImage (1 : K ≃+* K) W = W := by
  ext v
  rfl

theorem coordImage_mul (σ τ : K ≃+* K) (W : Submodule K (ι → K)) :
    coordImage (σ * τ) W = coordImage σ (coordImage τ W) := by
  ext v
  rfl

theorem coordImage_span_singleton (σ : K ≃+* K) (v : ι → K) :
    coordImage σ (K ∙ v) = K ∙ (fun a => σ (v a)) := by
  ext u
  rw [mem_coordImage, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨σ c, funext fun a => ?_⟩
    have := congrFun hc a
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← map_mul, this, RingEquiv.apply_symm_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨σ.symm c, funext fun a => ?_⟩
    simp

variable [Fintype ι] [DecidableEq ι]

@[expose] def glAut : (K ≃+* K) →* MulAut (GL ι K) where
  toFun σ := Units.mapEquiv (RingEquiv.mapMatrix (m := ι) σ).toMulEquiv
  map_one' := by
    ext g i j
    rfl
  map_mul' σ τ := by
    ext g i j
    rfl

theorem coe_glAut (σ : K ≃+* K) (g : GL ι K) :
    ((glAut σ g : GL ι K) : Matrix ι ι K) = (g : Matrix ι ι K).map σ :=
  rfl

theorem coordImage_smul (σ : K ≃+* K) (B : GL ι K) (W : Submodule K (ι → K)) :
    coordImage σ (B • W) = glAut σ B • coordImage σ W := by
  ext v
  rw [mem_coordImage]
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).trans
    (Iff.trans ?_ (Submodule.mem_smul_pointwise_iff_exists _ _ _).symm)
  constructor
  · rintro ⟨w, hw, hBw⟩
    refine ⟨fun a => σ (w a), by simpa [mem_coordImage] using hw, ?_⟩
    change ((glAut σ B : GL ι K) : Matrix ι ι K) *ᵥ (fun a => σ (w a)) = v
    rw [coe_glAut]
    funext a
    have := RingHom.map_mulVec (σ : K →+* K) (B : Matrix ι ι K) w a
    change ((B : Matrix ι ι K) *ᵥ w) = fun a => σ.symm (v a) at hBw
    rw [hBw] at this
    simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at this
    exact this.symm
  · rintro ⟨u, hu, hBu⟩
    refine ⟨fun a => σ.symm (u a), hu, ?_⟩
    change ((glAut σ B : GL ι K) : Matrix ι ι K) *ᵥ u = v at hBu
    rw [coe_glAut] at hBu
    change (B : Matrix ι ι K) *ᵥ (fun a => σ.symm (u a)) = fun a => σ.symm (v a)
    funext a
    have := RingHom.map_mulVec (σ.symm : K →+* K) ((B : Matrix ι ι K).map σ) u a
    rw [hBu] at this
    have hBB : ((B : Matrix ι ι K).map σ).map (σ.symm : K →+* K) = B := by
      ext i j
      simp
    rw [hBB] at this
    exact this.symm

end Coord

section SemiGL

variable (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K]

abbrev SemiGL : Type := GL ι K ⋊[glAut] (K ≃+* K)

variable {ι K}

noncomputable instance semiGLAction : MulAction (SemiGL ι K) (Submodule K (ι → K)) where
  smul x W := x.left • coordImage x.right W
  one_smul W := by
    change (1 : GL ι K) • coordImage 1 W = W
    rw [coordImage_one, one_smul]
  mul_smul x y W := by
    change (x * y).left • coordImage (x * y).right W =
      x.left • coordImage x.right (y.left • coordImage y.right W)
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, coordImage_mul,
      coordImage_smul, mul_smul]

theorem semiGL_smul_def (x : SemiGL ι K) (W : Submodule K (ι → K)) :
    x • W = x.left • coordImage x.right W :=
  rfl

theorem semiGL_conj_inl (x : SemiGL ι K) (g : GL ι K) :
    x * SemidirectProduct.inl g * x⁻¹ =
      SemidirectProduct.inl (x.left * glAut x.right g * x.left⁻¹) := by
  apply SemidirectProduct.ext
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, mul_one, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, MulAut.one_apply]
  · simp

end SemiGL

variable {p f : ℕ} {K : Type} [Field K]

theorem map_bar_comm (h : UnitaryFieldData p f K) (σ : K ≃+* K) (c : K) :
    σ (h.bar c) = h.bar (σ c) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]

theorem hypGram_map_ringEquiv {r ε : ℕ} (σ : K ≃+* K) :
    (hypGram r ε K).map σ = hypGram r ε K :=
  hypGram_map (σ : K →+* K)

theorem map_conjTranspose_mul_mul {r ε : ℕ} (h : UnitaryFieldData p f K) (σ : K ≃+* K)
    (A G : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    (((A.map h.bar)ᵀ * G * A).map σ) =
      ((A.map σ).map h.bar)ᵀ * G.map σ * A.map σ := by
  rw [Matrix.map_mul, Matrix.map_mul, transpose_map]
  congr 3
  ext i j
  simp [map_bar_comm]

theorem map_similitude {r ε : ℕ} (h : UnitaryFieldData p f K)
    {A : Matrix (HypIndex r ε) (HypIndex r ε) K} {μ : K}
    (hA : (A.map h.bar)ᵀ * hypGram r ε K * A = μ • hypGram r ε K) (σ : K ≃+* K) :
    ((A.map σ).map h.bar)ᵀ * hypGram r ε K * A.map σ = σ μ • hypGram r ε K := by
  have := congrArg (Matrix.map · σ) hA
  rw [map_conjTranspose_mul_mul, hypGram_map_ringEquiv, Matrix.map_smul' _ _ _ (map_mul σ),
    hypGram_map_ringEquiv] at this
  exact this

theorem inv_similitude {r ε : ℕ} (h : UnitaryFieldData p f K)
    {A B : Matrix (HypIndex r ε) (HypIndex r ε) K} {μ : K} (hμ0 : μ ≠ 0)
    (hA : (A.map h.bar)ᵀ * hypGram r ε K * A = μ • hypGram r ε K) (hAB : A * B = 1) :
    (B.map h.bar)ᵀ * hypGram r ε K * B = μ⁻¹ • hypGram r ε K := by
  have h1 := conjTranspose_mul_mul h (hypGram r ε K) A B
  rw [hA, hAB, Matrix.mul_smul, Matrix.smul_mul] at h1
  simp only [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one,
    Matrix.one_mul, Matrix.mul_one] at h1
  conv_rhs => rw [h1]
  rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]

variable (h : UnitaryFieldData p f K) (r ε : ℕ)

@[expose] def semilinearSimilitudes : Subgroup (SemiGL (HypIndex r ε) K) where
  carrier := {x | ∃ μ : K, μ ≠ 0 ∧ h.bar μ = μ ∧
    (((x.left : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ *
      hypGram r ε K * (x.left : Matrix (HypIndex r ε) (HypIndex r ε) K) = μ • hypGram r ε K}
  mul_mem' {x y} hx hy := by
    obtain ⟨μ, hμ0, hμ, hx⟩ := hx
    obtain ⟨ν, hν0, hν, hy⟩ := hy
    refine ⟨μ * x.right ν, mul_ne_zero hμ0 (by simpa using hν0), ?_, ?_⟩
    · rw [map_mul, hμ, ← map_bar_comm, hν]
    · rw [SemidirectProduct.mul_left, Units.val_mul, coe_glAut, conjTranspose_mul_mul, hx,
        Matrix.mul_smul, Matrix.smul_mul, map_similitude h hy, smul_smul]
  one_mem' := ⟨1, one_ne_zero, map_one _, by simp⟩
  inv_mem' {x} hx := by
    obtain ⟨μ, hμ0, hμ, hx⟩ := hx
    have hAB : ((x.left : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((x.left⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hB := inv_similitude h hμ0 hx hAB
    refine ⟨x.right⁻¹ μ⁻¹, by simpa using hμ0, ?_, ?_⟩
    · rw [← map_bar_comm, map_inv₀, hμ]
    · rw [SemidirectProduct.inv_left, coe_glAut]
      exact map_similitude h hB _

variable {h r ε}

theorem mem_semilinearSimilitudes {x : SemiGL (HypIndex r ε) K} :
    x ∈ semilinearSimilitudes h r ε ↔ ∃ μ : K, μ ≠ 0 ∧ h.bar μ = μ ∧
      (((x.left : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ *
        hypGram r ε K * (x.left : Matrix (HypIndex r ε) (HypIndex r ε) K) =
          μ • hypGram r ε K :=
  Iff.rfl

theorem hypForm_coord (σ : K ≃+* K) (v w : HypIndex r ε → K) :
    hypForm h r ε (fun a => σ (v a)) (fun a => σ (w a)) = σ (hypForm h r ε v w) := by
  rw [hypForm_apply, hypForm_apply, map_sum]
  simp [map_bar_comm]

theorem gramForm_smul_gram {ι : Type} [Fintype ι] (c : K) (G : Matrix ι ι K) (x y : ι → K) :
    gramForm h (c • G) x y = c * gramForm h G x y := by
  rw [gramForm_apply, gramForm_apply, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem semilinear_smul_mem {x : SemiGL (HypIndex r ε) K}
    (hx : x ∈ semilinearSimilitudes h r ε) {L : Submodule K (HypIndex r ε → K)}
    (hL : L ∈ hypIsotropicLines h r ε) : x • L ∈ hypIsotropicLines h r ε := by
  obtain ⟨μ, -, -, hx⟩ := hx
  obtain ⟨hL1, hL2⟩ := mem_hypIsotropicLines.mp hL
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ L, v ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h0 => ?_
    rw [h0, finrank_bot] at hL1
    exact zero_ne_one hL1
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hL1 hv hv0, semiGL_smul_def,
    coordImage_span_singleton]
  have hσv0 : (fun a => x.right (v a)) ≠ 0 := fun h0 =>
    hv0 (funext fun a => by simpa using congrFun h0 a)
  have hvv : hypForm h r ε v v = 0 := hL2 v hv
  rw [mem_hypIsotropicLines]
  refine ⟨?_, fun a ha => ?_⟩
  · exact (LinearEquiv.finrank_map_eq (DistribMulAction.toLinearEquiv K _ x.left) _).trans
      (finrank_span_singleton hσv0)
  · obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists a x.left _).mp ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have h0 : hypForm h r ε (c • fun a => x.right (v a)) (c • fun a => x.right (v a)) = 0 := by
      simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
        hypForm_coord, hvv, map_zero, mul_zero]
    change gramForm h (hypGram r ε K)
      ((x.left : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (c • fun a => x.right (v a)))
      ((x.left : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (c • fun a => x.right (v a))) = 0
    rw [gramForm_mulVec, hx, gramForm_smul_gram]
    change μ * hypForm h r ε (c • fun a => x.right (v a)) (c • fun a => x.right (v a)) = 0
    rw [h0, mul_zero]

noncomputable instance semilinearLineAction :
    MulAction (semilinearSimilitudes h r ε) (hypIsotropicLines h r ε) where
  smul x L := ⟨(x : SemiGL (HypIndex r ε) K) • (L : Submodule K (HypIndex r ε → K)),
    semilinear_smul_mem x.2 L.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul x y _ := Subtype.ext (mul_smul (x : SemiGL (HypIndex r ε) K) y _)

variable (h r ε)

@[expose] noncomputable def semilinearPointAction :
    semilinearSimilitudes h r ε →* Equiv.Perm (hypIsotropicLines h r ε) :=
  MulAction.toPermHom _ _

@[expose] noncomputable def semilinearPointGroup :
    Subgroup (Equiv.Perm (hypIsotropicLines h r ε)) :=
  (semilinearPointAction h r ε).range

variable {h r ε}

theorem semilinearPointAction_apply (x : semilinearSimilitudes h r ε)
    (L : hypIsotropicLines h r ε) :
    ((semilinearPointAction h r ε x L : hypIsotropicLines h r ε) :
      Submodule K (HypIndex r ε → K)) =
      (x : SemiGL (HypIndex r ε) K).left •
        coordImage (x : SemiGL (HypIndex r ε) K).right (L : Submodule K (HypIndex r ε → K)) :=
  rfl

theorem inl_mem_semilinearSimilitudes (g : hypSU h r ε) :
    SemidirectProduct.inl (g : GL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε :=
  ⟨1, one_ne_zero, map_one _, by rw [one_smul]; exact (mem_gramSU.mp g.2).1⟩

theorem hypProjLineAction_eq_semilinearPointAction (g : hypSU h r ε) :
    hypProjLineAction h r ε (hypProj h r ε g) =
      semilinearPointAction h r ε ⟨_, inl_mem_semilinearSimilitudes g⟩ := by
  refine Equiv.ext fun L => Subtype.ext ?_
  change g • (L : Submodule K (HypIndex r ε → K)) =
    (g : GL (HypIndex r ε) K) • coordImage 1 (L : Submodule K (HypIndex r ε → K))
  rw [coordImage_one]
  rfl

theorem hypProjLineAction_range_le :
    (hypProjLineAction h r ε).range ≤ semilinearPointGroup h r ε := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε x
  exact ⟨_, (hypProjLineAction_eq_semilinearPointAction g).symm⟩

theorem conj_mem_hypSU {x : SemiGL (HypIndex r ε) K} (hx : x ∈ semilinearSimilitudes h r ε)
    (g : hypSU h r ε) :
    x.left * glAut x.right (g : GL (HypIndex r ε) K) * x.left⁻¹ ∈ hypSU h r ε := by
  obtain ⟨μ, hμ0, -, hA⟩ := hx
  have hAB : ((x.left : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      ((x.left⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hB := inv_similitude h hμ0 hA hAB
  have hg0 : (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ *
      hypGram r ε K * ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        (1 : K) • hypGram r ε K := by
    rw [one_smul]
    exact (mem_gramSU.mp g.2).1
  have hg := map_similitude h hg0 x.right
  rw [map_one, one_smul] at hg
  have hdet : (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map
      x.right).det = 1 := by
    rw [show ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map x.right =
      (x.right : K →+* K).mapMatrix (g : GL (HypIndex r ε) K) from rfl, ← RingHom.map_det,
      (mem_gramSU.mp g.2).2, map_one]
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, coe_glAut, conjTranspose_mul_mul, conjTranspose_mul_mul,
      hA, Matrix.mul_smul, Matrix.smul_mul, hg, Matrix.mul_smul, Matrix.smul_mul, hB, smul_smul,
      mul_inv_cancel₀ hμ0, one_smul]
  · rw [Units.val_mul, Units.val_mul, coe_glAut, det_mul, det_mul, hdet, mul_one, ← det_mul,
      hAB, det_one]

theorem semilinearPointAction_conj (x : semilinearSimilitudes h r ε) (g : hypSU h r ε) :
    semilinearPointAction h r ε x * hypProjLineAction h r ε (hypProj h r ε g) *
      (semilinearPointAction h r ε x)⁻¹ =
    hypProjLineAction h r ε (hypProj h r ε ⟨_, conj_mem_hypSU x.2 g⟩) := by
  rw [hypProjLineAction_eq_semilinearPointAction, hypProjLineAction_eq_semilinearPointAction,
    ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (semiGL_conj_inl _ _))

theorem semilinearPointGroup_le_normalizer :
    semilinearPointGroup h r ε ≤
      Subgroup.normalizer ((hypProjLineAction h r ε).range : Set (Equiv.Perm _)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨g, rfl⟩ := hypProj_surjective h r ε z
    rw [semilinearPointAction_conj]
    exact ⟨_, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨g, rfl⟩ := hypProj_surjective h r ε z
    have hy : y = semilinearPointAction h r ε x⁻¹ * hypProjLineAction h r ε (hypProj h r ε g) *
        (semilinearPointAction h r ε x⁻¹)⁻¹ := by
      rw [hz, map_inv, inv_inv]
      group
    rw [hy, semilinearPointAction_conj]
    exact ⟨_, rfl⟩

theorem unitary_semilinear_point_data :
    (∀ (x : semilinearSimilitudes h r ε) (L : hypIsotropicLines h r ε),
      ((semilinearPointAction h r ε x L : hypIsotropicLines h r ε) :
        Submodule K (HypIndex r ε → K)) =
        (x : SemiGL (HypIndex r ε) K).left •
          coordImage (x : SemiGL (HypIndex r ε) K).right
            (L : Submodule K (HypIndex r ε → K))) ∧
    (hypProjLineAction h r ε).range ≤ semilinearPointGroup h r ε ∧
    semilinearPointGroup h r ε ≤
      Subgroup.normalizer ((hypProjLineAction h r ε).range : Set (Equiv.Perm _)) :=
  ⟨semilinearPointAction_apply, hypProjLineAction_range_le, semilinearPointGroup_le_normalizer⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

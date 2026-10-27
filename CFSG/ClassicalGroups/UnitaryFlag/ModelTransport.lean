module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.ClassicalGroups.UnitaryFlag.IsotropicKernel

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] def IsHypTransport (h : UnitaryFieldData p f K)
    (R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K) : Prop :=
  (R.map h.bar)ᵀ * R = hypGram r ε K

@[expose] noncomputable def transportInv (h : UnitaryFieldData p f K)
    (R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K) : Matrix (HypIndex r ε) (Fin (2 * r + ε)) K :=
  hypGram r ε K * (R.map h.bar)ᵀ

theorem card_hypIndex : Fintype.card (HypIndex r ε) = 2 * r + ε := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem transportInv_mul {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R) :
    transportInv h R * R = 1 := by
  rw [transportInv, Matrix.mul_assoc, hR, hypGram_mul_self]

theorem mul_transportInv {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R) :
    R * transportInv h R = 1 := by
  set e : HypIndex r ε ≃ Fin (2 * r + ε) := Fintype.equivFinOfCardEq card_hypIndex
  have h1 : (transportInv h R).submatrix e.symm (Equiv.refl _) *
      R.submatrix (Equiv.refl _) e.symm = 1 := by
    rw [submatrix_mul_equiv, transportInv_mul hR, submatrix_one_equiv]
  have h2 := mul_eq_one_comm.mp h1
  rw [submatrix_mul_equiv] at h2
  simpa using h2

theorem det_mul_mul_of_mul_eq_one {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι]
    [DecidableEq ι] (e : ι ≃ m) {A : Matrix m ι K} {B : Matrix ι m K} (hAB : A * B = 1)
    (M : Matrix ι ι K) : (A * M * B).det = M.det := by
  have hAB' : A.submatrix (Equiv.refl m) e.symm * B.submatrix e.symm (Equiv.refl m) = 1 := by
    rw [submatrix_mul_equiv, hAB, submatrix_one_equiv]
  have hM : A * M * B = A.submatrix (Equiv.refl m) e.symm * M.submatrix e.symm e.symm *
      B.submatrix e.symm (Equiv.refl m) := by
    rw [submatrix_mul_equiv, submatrix_mul_equiv]
    simp
  rw [hM, det_mul, det_mul, det_submatrix_equiv_self, mul_comm (det _) M.det, mul_assoc,
    ← det_mul, hAB', det_one, mul_one]

theorem stdHermForm_transport {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (x y : HypIndex r ε → K) :
    stdHermForm h (2 * r + ε) (R *ᵥ x) (R *ᵥ y) = hypForm h r ε x y := by
  rw [stdHermForm_eq_gramForm, gramForm_mulVec, Matrix.mul_one,
    show (R.map h.bar)ᵀ * R = hypGram r ε K from hR]

theorem hypForm_transportInv {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (u v : Fin (2 * r + ε) → K) :
    hypForm h r ε (transportInv h R *ᵥ u) (transportInv h R *ᵥ v) =
      stdHermForm h (2 * r + ε) u v := by
  rw [← stdHermForm_transport hR, mulVec_mulVec, mulVec_mulVec, mul_transportInv hR, one_mulVec,
    one_mulVec]

theorem exists_isHypTransport (h : UnitaryFieldData p f K) :
    ∃ R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K, IsHypTransport h R := by
  obtain ⟨w, hw⟩ := exists_hypBasis h (stdHermForm_isSymm h (2 * r + ε))
    (stdHermForm_separatingLeft h (2 * r + ε)) (r := r) (ε := ε) (Module.finrank_fin_fun K)
  refine ⟨Matrix.of fun k x => w x k, ?_⟩
  ext x y
  rw [← hw x y, stdHermForm_apply, mul_apply]
  rfl

section Conj

variable {h : UnitaryFieldData p f K} {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}

theorem transport_mul_mul (hR : IsHypTransport h R) (M N : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    R * M * transportInv h R * (R * N * transportInv h R) = R * (M * N) * transportInv h R := by
  rw [show R * M * transportInv h R * (R * N * transportInv h R) =
    R * M * (transportInv h R * R) * N * transportInv h R by simp only [Matrix.mul_assoc],
    transportInv_mul hR, Matrix.mul_one, Matrix.mul_assoc R M N]

theorem transportInv_mul_mul (hR : IsHypTransport h R)
    (M N : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) :
    transportInv h R * M * R * (transportInv h R * N * R) = transportInv h R * (M * N) * R := by
  rw [show transportInv h R * M * R * (transportInv h R * N * R) =
    transportInv h R * M * (R * transportInv h R) * N * R by simp only [Matrix.mul_assoc],
    mul_transportInv hR, Matrix.mul_one, Matrix.mul_assoc (transportInv h R) M N]

theorem transport_one (hR : IsHypTransport h R) :
    R * (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) * transportInv h R = 1 := by
  rw [Matrix.mul_one, mul_transportInv hR]

theorem transportInv_one (hR : IsHypTransport h R) :
    transportInv h R * (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * R = 1 := by
  rw [Matrix.mul_one, transportInv_mul hR]

@[expose] noncomputable def transportGL (hR : IsHypTransport h R) (g : GL (HypIndex r ε) K) :
    GL (Fin (2 * r + ε)) K where
  val := R * (g : Matrix (HypIndex r ε) (HypIndex r ε) K) * transportInv h R
  inv := R * ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
    transportInv h R
  val_inv := by
    rw [transport_mul_mul hR, ← Units.val_mul, mul_inv_cancel, Units.val_one, transport_one hR]
  inv_val := by
    rw [transport_mul_mul hR, ← Units.val_mul, inv_mul_cancel, Units.val_one, transport_one hR]

@[expose] noncomputable def transportGLInv (hR : IsHypTransport h R) (g : GL (Fin (2 * r + ε)) K) :
    GL (HypIndex r ε) K where
  val := transportInv h R * (g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * R
  inv := transportInv h R *
    ((g⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * R
  val_inv := by
    rw [transportInv_mul_mul hR, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      transportInv_one hR]
  inv_val := by
    rw [transportInv_mul_mul hR, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      transportInv_one hR]

theorem coe_transportGL (hR : IsHypTransport h R) (g : GL (HypIndex r ε) K) :
    ((transportGL hR g : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
      R * (g : Matrix (HypIndex r ε) (HypIndex r ε) K) * transportInv h R :=
  rfl

theorem coe_transportGLInv (hR : IsHypTransport h R) (g : GL (Fin (2 * r + ε)) K) :
    ((transportGLInv hR g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      transportInv h R * (g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * R :=
  rfl

theorem transportGL_mem (hR : IsHypTransport h R) (g : hypSU h r ε) :
    transportGL hR g ∈ unitarySU p f K (2 * r + ε) := by
  refine (mem_unitarySU_iff_isometry h).mpr ⟨?_, fun x y => ?_⟩
  · rw [coe_transportGL, det_mul_mul_of_mul_eq_one (Fintype.equivFinOfCardEq card_hypIndex)
      (mul_transportInv hR)]
    exact (mem_hypSU.mp g.2).2
  · rw [coe_transportGL, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      stdHermForm_transport hR]
    exact (hypForm_smul_smul h g _ _).trans (hypForm_transportInv hR x y)

theorem transportGLInv_mem (hR : IsHypTransport h R) (g : unitarySU p f K (2 * r + ε)) :
    transportGLInv hR g ∈ hypSU h r ε := by
  refine mem_gramSU_iff_isometry.mpr ⟨fun x y => ?_, ?_⟩
  · rw [coe_transportGLInv, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      hypForm_transportInv hR]
    exact (stdHermForm_smul_smul h g _ _).trans (stdHermForm_transport hR x y)
  · rw [coe_transportGLInv, det_mul_mul_of_mul_eq_one
      (Fintype.equivFinOfCardEq card_hypIndex).symm (transportInv_mul hR)]
    exact ((mem_unitarySU_iff h).mp g.2).1

theorem transportInv_transport (hR : IsHypTransport h R)
    (M : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    transportInv h R * (R * M * transportInv h R) * R = M := by
  rw [show transportInv h R * (R * M * transportInv h R) * R =
      (transportInv h R * R) * M * (transportInv h R * R) by simp only [Matrix.mul_assoc],
    transportInv_mul hR, Matrix.one_mul, Matrix.mul_one]

theorem transport_transportInv (hR : IsHypTransport h R)
    (N : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) :
    R * (transportInv h R * N * R) * transportInv h R = N := by
  rw [show R * (transportInv h R * N * R) * transportInv h R =
      (R * transportInv h R) * N * (R * transportInv h R) by simp only [Matrix.mul_assoc],
    mul_transportInv hR, Matrix.one_mul, Matrix.mul_one]

variable (h) in
@[expose] noncomputable def hypTransport (hR : IsHypTransport h R) :
    hypSU h r ε ≃* unitarySU p f K (2 * r + ε) where
  toFun g := ⟨transportGL hR g, transportGL_mem hR g⟩
  invFun g := ⟨transportGLInv hR g, transportGLInv_mem hR g⟩
  left_inv _ := Subtype.ext (Units.ext (transportInv_transport hR _))
  right_inv _ := Subtype.ext (Units.ext (transport_transportInv hR _))
  map_mul' _ _ := Subtype.ext (Units.ext (transport_mul_mul hR _ _).symm)

theorem coe_hypTransport (hR : IsHypTransport h R) (g : hypSU h r ε) :
    (((hypTransport h hR g : unitarySU p f K (2 * r + ε)) : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
        R * ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          transportInv h R :=
  rfl

theorem coe_hypTransport_symm (hR : IsHypTransport h R) (g : unitarySU p f K (2 * r + ε)) :
    ((((hypTransport h hR).symm g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
        transportInv h R * ((g : GL (Fin (2 * r + ε)) K) :
          Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * R :=
  rfl

theorem transport_scalar (hR : IsHypTransport h R) (c : K) :
    R * Matrix.scalar (HypIndex r ε) c * transportInv h R = Matrix.scalar (Fin (2 * r + ε)) c := by
  rw [scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    mul_transportInv hR, scalar_apply, ← smul_one_eq_diagonal]

theorem transportInv_scalar (hR : IsHypTransport h R) (c : K) :
    transportInv h R * Matrix.scalar (Fin (2 * r + ε)) c * R = Matrix.scalar (HypIndex r ε) c := by
  rw [scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    transportInv_mul hR, scalar_apply, ← smul_one_eq_diagonal]

theorem mem_hypScalars_iff_transport (hR : IsHypTransport h R) (g : hypSU h r ε) :
    g ∈ hypScalars h r ε ↔ hypTransport h hR g ∈ unitaryScalars h (2 * r + ε) := by
  constructor
  · rintro ⟨c, hc, hcn, hg⟩
    refine ⟨c, hc, hcn, Units.ext ?_⟩
    rw [coe_hypTransport, hg, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
      transport_scalar hR]
  · rintro ⟨c, hc, hcn, hg⟩
    refine ⟨c, hc, hcn, Units.ext ?_⟩
    have := congrArg (fun g : GL (Fin (2 * r + ε)) K =>
      transportInv h R * (g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * R) hg
    simp only [coe_hypTransport, GeneralLinearGroup.coe_scalar, transportInv_scalar hR] at this
    rw [GeneralLinearGroup.coe_scalar, ← this]
    simp only [Matrix.mul_assoc]
    rw [transportInv_mul hR, ← Matrix.mul_assoc, transportInv_mul hR, Matrix.one_mul,
      Matrix.mul_one]

theorem map_hypScalars_hypTransport (hR : IsHypTransport h R) :
    (hypScalars h r ε).map (hypTransport h hR : hypSU h r ε →* unitarySU p f K (2 * r + ε)) =
      unitaryScalars h (2 * r + ε) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_hypScalars_iff_transport hR g).mp hg
  · intro hx
    refine ⟨(hypTransport h hR).symm x, (mem_hypScalars_iff_transport hR _).mpr ?_,
      MulEquiv.apply_symm_apply _ _⟩
    rwa [MulEquiv.apply_symm_apply]

variable (h) in
@[expose] noncomputable def hypProjTransport (hR : IsHypTransport h R) :
    hypPSU h r ε ≃* unitaryPSU h (2 * r + ε) :=
  QuotientGroup.congr _ _ (hypTransport h hR) (map_hypScalars_hypTransport hR)

theorem hypProjTransport_hypProj (hR : IsHypTransport h R) (g : hypSU h r ε) :
    hypProjTransport h hR (hypProj h r ε g) = unitaryProj h (2 * r + ε) (hypTransport h hR g) :=
  QuotientGroup.congr_mk _ _ _ _ g

variable (h) in
@[expose] noncomputable def hypPSUEquivStatedProj (hR : IsHypTransport h R)
    (hn : 1 ≤ 2 * r + ε) : hypPSU h r ε ≃* StatedProj (StatedSU (2 * r + ε) (p ^ f) K) :=
  (hypProjTransport h hR).trans (unitaryPSUEquiv h hn)

theorem hypPSUEquivStatedProj_hypProj (hR : IsHypTransport h R) (hn : 1 ≤ 2 * r + ε)
    (g : hypSU h r ε) :
    hypPSUEquivStatedProj h hR hn (hypProj h r ε g) =
      (QuotientGroup.mk (hypTransport h hR g : StatedSU (2 * r + ε) (p ^ f) K) :
        StatedProj (StatedSU (2 * r + ε) (p ^ f) K)) := by
  rw [hypPSUEquivStatedProj, MulEquiv.trans_apply, hypProjTransport_hypProj,
    unitaryPSUEquiv_unitaryProj]

variable (h) in
@[expose] noncomputable def transportEquiv (hR : IsHypTransport h R) :
    (HypIndex r ε → K) ≃ₗ[K] (Fin (2 * r + ε) → K) :=
  LinearEquiv.ofLinearMap (mulVecLin R) (mulVecLin (transportInv h R))
    (by rw [← mulVecLin_mul, mul_transportInv hR, mulVecLin_one])
    (by rw [← mulVecLin_mul, transportInv_mul hR, mulVecLin_one])

variable (h) in
@[expose] noncomputable def transportSubspace (hR : IsHypTransport h R) :
    Submodule K (HypIndex r ε → K) ≃o Submodule K (Fin (2 * r + ε) → K) :=
  Submodule.orderIsoMapComap (transportEquiv h hR)

theorem transportSubspace_apply (hR : IsHypTransport h R) (W : Submodule K (HypIndex r ε → K)) :
    transportSubspace h hR W = W.map (mulVecLin R) :=
  rfl

theorem finrank_transportSubspace (hR : IsHypTransport h R)
    (W : Submodule K (HypIndex r ε → K)) :
    Module.finrank K (transportSubspace h hR W) = Module.finrank K W :=
  LinearEquiv.finrank_map_eq (transportEquiv h hR) W

theorem isTotallyIsotropic_transportSubspace (hR : IsHypTransport h R)
    (W : Submodule K (HypIndex r ε → K)) :
    (∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) ↔
      ∀ x ∈ transportSubspace h hR W, ∀ y ∈ transportSubspace h hR W,
        stdHermForm h (2 * r + ε) x y = 0 := by
  constructor
  · rintro hW _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change stdHermForm h _ (R *ᵥ x) (R *ᵥ y) = 0
    rw [stdHermForm_transport hR]
    exact hW x hx y hy
  · intro hW x hx y hy
    rw [← stdHermForm_transport hR]
    exact hW _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

theorem isotropic_transportSubspace (hR : IsHypTransport h R)
    (W : Submodule K (HypIndex r ε → K)) :
    (∀ x ∈ W, hypForm h r ε x x = 0) ↔
      ∀ x ∈ transportSubspace h hR W, stdHermForm h (2 * r + ε) x x = 0 := by
  constructor
  · rintro hW _ ⟨x, hx, rfl⟩
    change stdHermForm h _ (R *ᵥ x) (R *ᵥ x) = 0
    rw [stdHermForm_transport hR]
    exact hW x hx
  · intro hW x hx
    rw [← stdHermForm_transport hR]
    exact hW _ ⟨x, hx, rfl⟩

theorem transportSubspace_smul (hR : IsHypTransport h R) (g : hypSU h r ε)
    (W : Submodule K (HypIndex r ε → K)) :
    transportSubspace h hR (g • W) = hypTransport h hR g • transportSubspace h hR W := by
  rw [transportSubspace_apply, transportSubspace_apply, Subgroup.smul_def, Subgroup.smul_def,
    smul_eq_map, smul_eq_map, ← Submodule.map_comp, ← Submodule.map_comp, ← mulVecLin_mul,
    ← mulVecLin_mul, coe_hypTransport]
  congr 2
  rw [Matrix.mul_assoc, transportInv_mul hR, Matrix.mul_one]

end Conj

@[expose] def hypIsotropicLines (h : UnitaryFieldData p f K) (r ε : ℕ) :
    SubMulAction (hypSU h r ε) (Submodule K (HypIndex r ε → K)) where
  carrier := {L | Module.finrank K L = 1 ∧ ∀ a ∈ L, hypForm h r ε a a = 0}
  smul_mem' g L hL := by
    refine ⟨?_, fun a ha => ?_⟩
    · rw [← hL.1]
      exact LinearEquiv.finrank_map_eq (DistribMulAction.toLinearEquiv K _ g) L
    · obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists a g L).mp ha
      rw [hypForm_smul_smul]
      exact hL.2 b hb

theorem mem_hypIsotropicLines {h : UnitaryFieldData p f K} {L : Submodule K (HypIndex r ε → K)} :
    L ∈ hypIsotropicLines h r ε ↔ Module.finrank K L = 1 ∧ ∀ a ∈ L, hypForm h r ε a a = 0 :=
  Iff.rfl

theorem transportSubspace_mem_isotropicLines {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (L : Submodule K (HypIndex r ε → K)) :
    transportSubspace h hR L ∈ isotropicLines h (2 * r + ε) ↔ L ∈ hypIsotropicLines h r ε := by
  rw [mem_isotropicLines, mem_hypIsotropicLines, finrank_transportSubspace,
    isotropic_transportSubspace hR]

theorem mem_ker_toPermHom_iff {G α : Type*} [Group G] [MulAction G α] {g : G} :
    g ∈ (MulAction.toPermHom G α).ker ↔ ∀ a : α, g • a = a := by
  rw [MonoidHom.mem_ker, Equiv.ext_iff]
  rfl

theorem ker_hypIsotropicLines (h : UnitaryFieldData p f K) (hn : 2 ≤ 2 * r + ε) :
    (MulAction.toPermHom (hypSU h r ε) (hypIsotropicLines h r ε)).ker = hypScalars h r ε := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  ext g
  rw [mem_hypScalars_iff_transport hR, ← unitary_isotropic_kernel h hn, mem_ker_toPermHom_iff,
    mem_ker_toPermHom_iff]
  constructor
  · rintro hg ⟨L', hL'⟩
    obtain ⟨L, rfl⟩ := (transportSubspace h hR).surjective L'
    have hL := (transportSubspace_mem_isotropicLines hR L).mp hL'
    have := congrArg Subtype.val (hg ⟨L, hL⟩)
    refine Subtype.ext ?_
    change hypTransport h hR g • transportSubspace h hR L = transportSubspace h hR L
    rw [← transportSubspace_smul]
    exact congrArg _ this
  · rintro hg ⟨L, hL⟩
    have hL' := (transportSubspace_mem_isotropicLines hR L).mpr hL
    have := congrArg Subtype.val (hg ⟨_, hL'⟩)
    refine Subtype.ext ((transportSubspace h hR).injective ?_)
    change transportSubspace h hR (g • L) = transportSubspace h hR L
    rw [transportSubspace_smul]
    exact this

@[expose] noncomputable def hypProjLineAction (h : UnitaryFieldData p f K) (r ε : ℕ) :
    hypPSU h r ε →* Equiv.Perm (hypIsotropicLines h r ε) :=
  QuotientGroup.lift (hypScalars h r ε) (MulAction.toPermHom _ _) fun _ hg =>
    Equiv.ext fun L => Subtype.ext (smul_submodule_of_mem_normOneScalars hg L)

theorem hypProjLineAction_injective (h : UnitaryFieldData p f K) (hn : 2 ≤ 2 * r + ε) :
    Function.Injective (hypProjLineAction h r ε) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (hypScalars h r ε) x
  have hx' : MulAction.toPermHom (hypSU h r ε) (hypIsotropicLines h r ε) g = 1 := hx
  have hg : g ∈ hypScalars h r ε := by
    rw [← ker_hypIsotropicLines h hn]
    exact hx'
  exact (QuotientGroup.eq_one_iff g).mpr hg

theorem card_hypScalars (h : UnitaryFieldData p f K) (hn : 1 ≤ 2 * r + ε) :
    Nat.card (hypScalars h r ε) = Nat.gcd (2 * r + ε) (p ^ f + 1) := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  rw [← card_unitaryScalars h hn, ← map_hypScalars_hypTransport hR]
  exact Nat.card_congr ((hypTransport h hR).subgroupMap _).toEquiv

theorem not_dvd_gcd_pow_add_one (h : UnitaryFieldData p f K) (n : ℕ) :
    ¬ p ∣ Nat.gcd n (p ^ f + 1) := by
  intro hp
  have h1 : p ∣ p ^ f + 1 := hp.trans (Nat.gcd_dvd_right _ _)
  have h2 : p ∣ 1 := (Nat.dvd_add_right (dvd_pow_self p (by have := h.one_le; omega))).mp h1
  exact h.prime.one_lt.ne' (Nat.dvd_one.mp h2)

theorem unitary_hyperbolic_model_transport (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) :
    (∃ R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K, (R.map h.bar)ᵀ * R = hypGram r ε K) ∧
    (∀ (R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K) (hR : IsHypTransport h R),
      (R * transportInv h R = 1 ∧ transportInv h R * R = 1) ∧
      (∀ g : hypSU h r ε, (((hypTransport h hR g : unitarySU p f K (2 * r + ε)) :
          GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
        R * ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          transportInv h R) ∧
      (hypScalars h r ε).map (hypTransport h hR : hypSU h r ε →* unitarySU p f K (2 * r + ε)) =
        unitaryScalars h (2 * r + ε) ∧
      (∀ g : hypSU h r ε, hypProjTransport h hR (hypProj h r ε g) =
        unitaryProj h (2 * r + ε) (hypTransport h hR g)) ∧
      (∀ W : Submodule K (HypIndex r ε → K), transportSubspace h hR W = W.map (mulVecLin R)) ∧
      (∀ W : Submodule K (HypIndex r ε → K),
        Module.finrank K (transportSubspace h hR W) = Module.finrank K W) ∧
      (∀ W : Submodule K (HypIndex r ε → K), (∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) ↔
        ∀ x ∈ transportSubspace h hR W, ∀ y ∈ transportSubspace h hR W,
          stdHermForm h (2 * r + ε) x y = 0) ∧
      (∀ (g : hypSU h r ε) (W : Submodule K (HypIndex r ε → K)),
        transportSubspace h hR (g • W) = hypTransport h hR g • transportSubspace h hR W)) ∧
    (MulAction.toPermHom (hypSU h r ε) (hypIsotropicLines h r ε)).ker = hypScalars h r ε ∧
    Function.Injective (hypProjLineAction h r ε) ∧
    Nat.card (hypScalars h r ε) = Nat.gcd (2 * r + ε) (p ^ f + 1) ∧
    ¬ p ∣ Nat.card (hypScalars h r ε) := by
  have hn : 2 ≤ 2 * r + ε := by omega
  have hcard := card_hypScalars h (r := r) (ε := ε) (by omega)
  refine ⟨exists_isHypTransport h, fun R hR => ⟨⟨mul_transportInv hR, transportInv_mul hR⟩,
    coe_hypTransport hR, map_hypScalars_hypTransport hR, hypProjTransport_hypProj hR,
    transportSubspace_apply hR, finrank_transportSubspace hR,
    isTotallyIsotropic_transportSubspace hR, transportSubspace_smul hR⟩,
    ker_hypIsotropicLines h hn, hypProjLineAction_injective h hn, hcard, ?_⟩
  rw [hcard]
  exact not_dvd_gcd_pow_add_one h _

end CFSG.ClassicalGroups.UnitaryFlag

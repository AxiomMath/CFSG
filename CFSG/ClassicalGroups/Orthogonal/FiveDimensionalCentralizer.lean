module

public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareEigenspaces
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquarePositive

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel

open Matrix QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} (F : FrameData Q)

abbrev zOp : Module.End K V := (F.z : V →ₗ[K] V)

abbrev U : Submodule K V := zOp F |>.eigenspace (-1)

abbrev W : Submodule K V := zOp F |>.eigenspace 1

theorem zOp_mul_self : zOp F * zOp F = (1 : K) ^ 2 • (1 : Module.End K V) := by
  rw [one_pow, one_smul]
  exact congrArg (fun g : V ≃ₗ[K] V => (g : V →ₗ[K] V)) F.z_mul_self

theorem zOp_selfAdjoint (x y : V) :
    Q.polarBilin (zOp F x) y = Q.polarBilin x (zOp F y) := by
  have hz2 : ∀ v, zOp F (zOp F v) = v := by
    intro v
    have h := congrArg (fun g : V ≃ₗ[K] V => (g : V →ₗ[K] V)) F.z_mul_self
    exact LinearMap.congr_fun h v
  calc Q.polarBilin (zOp F x) y
      = Q.polarBilin (zOp F x) (zOp F (zOp F y)) := by rw [hz2]
    _ = Q.polarBilin x (zOp F y) :=
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem F.z_mem x (zOp F y)

@[simp] theorem zFun_apply (i : Fin 5) :
    F.zFun i = if (i : ℕ) < 4 then -Pi.single i 1 else Pi.single i 1 := rfl

theorem zCoord_apply_coord (c : Fin 5 → K) (j : Fin 5) :
    F.zCoord c j = if (j : ℕ) < 4 then -c j else c j := by
  rw [F.zCoord_apply]
  rw [show F.zLin = (Pi.basisFun K (Fin 5)).constr K F.zFun from rfl]
  rw [Module.Basis.constr_apply_fintype]
  simp only [Pi.basisFun_repr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zFun_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hj : (j : ℕ) < 4 <;> simp [hj]
  · intro i _ hij
    by_cases hi : (i : ℕ) < 4 <;>
      simp [hi, Pi.single_eq_of_ne (Ne.symm hij)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem coord_z (x : V) : F.coord (F.z x) = F.zCoord (F.coord x) := by
  rw [show F.z x = F.conjCoord F.zCoord x from rfl, F.conjCoord_apply,
    LinearEquiv.apply_symm_apply]

theorem W_eq_span_four : W F = Submodule.span K {F.e 4} := by
  ext x
  constructor
  · intro hx
    rw [W, Module.End.mem_eigenspace_iff, show zOp F x = F.z x from rfl, one_smul] at hx
    have hc : F.zCoord (F.coord x) = F.coord x := by
      rw [← coord_z F, hx]
    have h4 : ∀ i : Fin 5, (i : ℕ) < 4 → F.coord x i = 0 := by
      intro i hi
      have := congrArg (fun f : Fin 5 → K => f i) hc
      rw [zCoord_apply_coord F, if_pos hi] at this
      have h2 : (2 : K) * F.coord x i = 0 := by linear_combination -this
      exact (mul_eq_zero.mp h2).resolve_left F.two_ne_zero
    have hx4 : F.coord x = F.coord x 4 • (Pi.single 4 1 : Fin 5 → K) := by
      funext j
      by_cases hj : (j : ℕ) < 4
      · have hj4 : j ≠ 4 := by intro h; subst h; omega
        rw [h4 j hj]
        simp [hj4]
      · have hj4 : j = 4 := by ext; omega
        subst hj4
        simp
    rw [Submodule.mem_span_singleton]
    refine ⟨F.coord x 4, ?_⟩
    calc F.coord x 4 • F.e 4
        = F.coord.symm (F.coord x 4 • (Pi.single 4 1 : Fin 5 → K)) := by
          calc F.coord x 4 • F.e 4
              = F.coord x 4 • F.coord.symm (Pi.single 4 1) := by
                rw [F.coord_symm_single]
            _ = F.coord.symm (F.coord x 4 • Pi.single 4 1) :=
                (map_smul F.coord.symm (F.coord x 4) (Pi.single 4 1)).symm
      _ = F.coord.symm (F.coord x) := by
        conv_rhs => rw [hx4]
      _ = x := F.coord.symm_apply_apply x
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [W, Module.End.mem_eigenspace_iff, show zOp F (c • F.e 4) = F.z (c • F.e 4) from rfl,
      one_smul, map_smul, F.z_e 4]
    simp

theorem finrank_W : Module.finrank K (W F) = 1 := by
  rw [W_eq_span_four]
  exact finrank_span_singleton (F.e.ne_zero 4)

theorem W_nondegenerate : (Q.comp (W F).subtype).Nondegenerate := by
  let _ : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
  have hsym : LinearMap.BilinForm.IsSymm (polarBilin Q) :=
    LinearMap.BilinForm.isSymm_iff.mpr (CFSG.RankThree.Classical.isSymm_polarBilin Q)
  have h := (positive_adjoint_eigenspaces_nondegenerate (Q.polarBilin) F.nondeg
    hsym (zOp F) 1 one_ne_zero F.two_ne_zero (zOp_mul_self F) (zOp_selfAdjoint F)).1
  exact QuadraticMap.nondegenerate_polar_iff.mp h

theorem U_nondegenerate : (Q.comp (U F).subtype).Nondegenerate := by
  let _ : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
  have hsym : LinearMap.BilinForm.IsSymm (polarBilin Q) :=
    LinearMap.BilinForm.isSymm_iff.mpr (CFSG.RankThree.Classical.isSymm_polarBilin Q)
  have h := (positive_adjoint_eigenspaces_nondegenerate (Q.polarBilin) F.nondeg
    hsym (zOp F) 1 one_ne_zero F.two_ne_zero (zOp_mul_self F) (zOp_selfAdjoint F)).2
  exact QuadraticMap.nondegenerate_polar_iff.mp h

theorem W_polar_nondegenerate : (Q.comp (W F).subtype).polarBilin.Nondegenerate := by
  let _ : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
  exact QuadraticMap.nondegenerate_polar_iff.mpr (W_nondegenerate F)

theorem U_polar_nondegenerate : (Q.comp (U F).subtype).polarBilin.Nondegenerate := by
  let _ : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
  exact QuadraticMap.nondegenerate_polar_iff.mpr (U_nondegenerate F)

theorem finrank_U : Module.finrank K (U F) = 4 := by
  have hcompl := squareScalar_eigenspaces_isCompl (T := zOp F) 1 one_ne_zero F.two_ne_zero
    (zOp_mul_self F)
  have h := Submodule.finrank_add_eq_of_isCompl hcompl
  change Module.finrank K (W F) + Module.finrank K (U F) = Module.finrank K V at h
  have hV : Module.finrank K V = 5 := by
    rw [Module.finrank_eq_card_basis F.e]
    simp
  have hW := finrank_W F
  omega

def wVec : W F := ⟨F.e 4, by
  rw [W_eq_span_four F]
  exact Submodule.subset_span rfl⟩

theorem wVec_ne_zero : wVec F ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  exact F.e.ne_zero 4 (by simpa [wVec] using h')

private def wEquiv : K ≃ₗ[K] W F :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton K (W F) (wVec F)) (by
    constructor
    · intro a b hab
      have hab' : a • wVec F = b • wVec F := hab
      exact (smul_left_injective K (wVec_ne_zero F)) hab'
    · intro x
      have htop : Submodule.span K {wVec F} = ⊤ :=
        (finrank_eq_one_iff_of_nonzero (wVec F) (wVec_ne_zero F)).mp (finrank_W F)
      have hx : x ∈ Submodule.span K {wVec F} := by rw [htop]; trivial
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      exact ⟨a, rfl⟩)

private theorem wEquiv_one : wEquiv F 1 = wVec F := by
  change (LinearMap.toSpanSingleton K (W F) (wVec F)) 1 = wVec F
  simp [LinearMap.toSpanSingleton]

private def wBasis : Module.Basis (Fin 1) K (W F) :=
  (Module.Basis.singleton (Fin 1) K).map (wEquiv F)

private theorem wBasis_zero : wBasis F 0 = wVec F := by
  simp [wBasis, wEquiv_one]

private theorem det_eq_scalar_of_apply (g : (W F) ≃ₗ[K] (W F)) {b : K} (hb0 : b ≠ 0)
    (hb : g (wVec F) = b • wVec F) :
    LinearEquiv.det g = Units.mk0 b hb0 := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix (wBasis F) (g : (W F) →ₗ[K] (W F)),
    Matrix.det_unique]
  have hentry : LinearMap.toMatrix (wBasis F) (wBasis F) (g : (W F) →ₗ[K] (W F))
      (default : Fin 1) (default : Fin 1) = b := by
    rw [show (default : Fin 1) = 0 from rfl, LinearMap.toMatrix_apply, wBasis_zero]
    change (wBasis F).repr ((g : (W F) → (W F)) (wVec F)) 0 = b
    rw [show (g : (W F) → (W F)) (wVec F) = b • wVec F from hb]
    rw [← wBasis_zero F, map_smul, Module.Basis.repr_self]
    simp
  exact hentry

def scalarOnW (u : Kˣ) (hu : u * u = 1) :
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp (W F).subtype) where
  val := u • (1 : (W F) ≃ₗ[K] (W F))
  property := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    change Q ((u : K) • x.val) = Q x.val
    rw [QuadraticMap.map_smul]
    have hu' : ((u : K) * (u : K)) = 1 := by
      simpa using congrArg (fun z : Kˣ => (z : K)) hu
    simp only [pow_two, hu', one_smul]

theorem det_scalarOnW (u : Kˣ) (hu : u * u = 1) :
    LinearEquiv.det (scalarOnW (F := F) u hu).val = u := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have hmap : ((scalarOnW (F := F) u hu).val : (W F) →ₗ[K] (W F)) =
      (u : K) • LinearMap.id := by
    ext x
    rfl
  rw [hmap, LinearMap.det_smul, LinearMap.det_id, finrank_W F, pow_one, mul_one]

abbrev SO5 : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Q.specialOrthogonalWithin

abbrev H (F : FrameData Q) : Subgroup (SO5 (Q := Q)) :=
  Subgroup.centralizer ({F.zSO} : Set (SO5 (Q := Q)))

def soCentralizerToOperator (F : FrameData Q) :
    H F →* orthogonalOperatorCentralizer Q (zOp F) where
  toFun g :=
    ⟨g.val.val, by
      intro x
      have h := congrArg (fun s : SO5 (Q := Q) => (s : V ≃ₗ[K] V))
        (Subgroup.mem_centralizer_singleton_iff.mp g.property)
      have hx := LinearEquiv.congr_fun h x
      simpa [LinearEquiv.mul_apply, FrameData.zSO, FrameData.zO, Subgroup.coe_mk] using hx⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def restrictU (F : FrameData Q) :
    H F →* TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype) where
  toFun g := (splitOrthogonalRestriction Q (zOp F) 1 (soCentralizerToOperator F g)).2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem scalarOnW_congr {u v : Kˣ} (h : u = v)
    (hu : u * u = 1) (hv : v * v = 1) :
    scalarOnW (F := F) u hu = scalarOnW (F := F) v hv := by
  subst h
  congr 1

theorem eq_scalarOnW (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (W F).subtype))
    (hu : LinearEquiv.det g.val * LinearEquiv.det g.val = 1) :
    g = scalarOnW (F := F) (LinearEquiv.det g.val) hu := by
  have htop : Submodule.span K {wVec F} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero (wVec F) (wVec_ne_zero F)).mp (finrank_W F)
  obtain ⟨b, hb⟩ : ∃ b : K, g.val (wVec F) = b • wVec F := by
    have hx : g.val (wVec F) ∈ Submodule.span K {wVec F} := by rw [htop]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨a, ha.symm⟩
  have hb0 : b ≠ 0 := by
    intro h
    have hzero : g.val (wVec F) = 0 := by rw [hb, h, zero_smul]
    exact wVec_ne_zero F (g.val.map_eq_zero_iff.mp hzero)
  have hdet : LinearEquiv.det g.val = Units.mk0 b hb0 :=
    det_eq_scalar_of_apply F g hb0 hb
  have hact : ∀ x : W F, g.val x = b • x := by
    intro x
    have hx : x ∈ Submodule.span K {wVec F} := by rw [htop]; trivial
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hb, smul_smul, smul_smul, mul_comm]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [hact x]
  change b • x = ((LinearEquiv.det g.val : Kˣ) : K) • x
  rw [show ((LinearEquiv.det g.val : Kˣ) : K) = b from congrArg Units.val hdet]

theorem det_positiveOrthogonalExtension
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hadj : ∀ x y : V, Q.polarBilin (T x) y = Q.polarBilin x (T y))
    (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace b).subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace (-b)).subtype)) :
    LinearEquiv.det ((positiveOrthogonalExtension Q T b hb h2 hsquare hadj g).val.val) =
      LinearEquiv.det g.1.val * LinearEquiv.det g.2.val := by
  unfold positiveOrthogonalExtension splitCentralizerExtension
  rw [LinearEquiv.det_conj (f := g.1.val.prodCongr g.2.val)
    (e := squareScalar_eigenspaceEquiv T b hb h2 hsquare)]
  apply Units.ext
  rw [Units.val_mul, LinearEquiv.coe_det, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap,
    LinearEquiv.coe_det, LinearEquiv.coe_det]


def extendU (h : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) : H F := by
  let u : Kˣ := QuadraticMap.orthogonalDet (Q.comp (U F).subtype) h
  have hu : u * u = 1 := by
    let _ : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
    have hsep : LinearMap.SeparatingLeft (polarBilin (Q.comp (U F).subtype)) :=
      (QuadraticMap.nondegenerate_polar_iff.mpr (U_nondegenerate F)).1
    have hsq := TauCeti.QuadraticMap.orthogonalDet_sq (Q := Q.comp (U F).subtype) hsep h
    simpa [u, pow_two] using hsq
  let gW : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (W F).subtype) :=
    scalarOnW (F := F) u hu
  let gO : orthogonalOperatorCentralizer Q (zOp F) :=
    positiveOrthogonalExtension Q (zOp F) 1 one_ne_zero F.two_ne_zero (zOp_mul_self F)
      (zOp_selfAdjoint F) (gW, h)
  have hdet : LinearEquiv.det gO.val.val = 1 := by
    rw [det_positiveOrthogonalExtension]
    rw [det_scalarOnW]
    have hdh : LinearEquiv.det h.val = u := by
      simpa [u] using QuadraticMap.orthogonalDet_apply h
    rw [hdh, hu]
  let gSO : SO5 (Q := Q) := ⟨gO.val, by
    rw [QuadraticMap.mem_specialOrthogonalWithin_iff]
    exact hdet⟩
  refine ⟨gSO, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx := gO.property x
  simpa [LinearEquiv.mul_apply, zOp, FrameData.zSO, FrameData.zO, Subgroup.coe_mk] using hx

theorem extendU_restrictU (g : H F) : extendU F (restrictU F g) = g := by
  let gO := soCentralizerToOperator F g
  let gW : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (W F).subtype) :=
    (splitOrthogonalRestriction Q (zOp F) 1 gO).1
  let gU : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype) :=
    (splitOrthogonalRestriction Q (zOp F) 1 gO).2
  have hgU : gU = restrictU F g := rfl
  have hsplit : splitOrthogonalRestriction Q (zOp F) 1 gO = (gW, gU) := rfl
  have hpos : positiveOrthogonalExtension Q (zOp F) 1 one_ne_zero F.two_ne_zero
      (zOp_mul_self F) (zOp_selfAdjoint F) (gW, gU) = gO := by
    rw [← hsplit]
    exact positive_extension_splitOrthogonalRestriction Q (zOp F) 1 one_ne_zero F.two_ne_zero
      (zOp_mul_self F) (zOp_selfAdjoint F) gO
  have hgdet : LinearEquiv.det gO.val.val = 1 := by
    have := QuadraticMap.mem_specialOrthogonalWithin_iff.mp g.val.property
    simpa [gO, soCentralizerToOperator] using this
  have hprod : LinearEquiv.det gW.val * LinearEquiv.det gU.val = 1 := by
    have h := det_positiveOrthogonalExtension (Q := Q) (T := zOp F) (b := 1)
      one_ne_zero F.two_ne_zero (zOp_mul_self F) (zOp_selfAdjoint F) (gW, gU)
    rw [hpos, hgdet] at h
    exact h.symm
  have huU : LinearEquiv.det gU.val * LinearEquiv.det gU.val = 1 := by
    let _ : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
    have hsep : LinearMap.SeparatingLeft (polarBilin (Q.comp (U F).subtype)) :=
      (QuadraticMap.nondegenerate_polar_iff.mpr (U_nondegenerate F)).1
    have hsq := TauCeti.QuadraticMap.orthogonalDet_sq (Q := Q.comp (U F).subtype) hsep gU
    simpa [pow_two] using hsq
  have hdet_eq : LinearEquiv.det gW.val = LinearEquiv.det gU.val := by
    calc LinearEquiv.det gW.val
        = LinearEquiv.det gW.val * (LinearEquiv.det gU.val * LinearEquiv.det gU.val) := by
          rw [huU, mul_one]
      _ = (LinearEquiv.det gW.val * LinearEquiv.det gU.val) * LinearEquiv.det gU.val := by
          group
      _ = LinearEquiv.det gU.val := by rw [hprod, one_mul]
  have huW : LinearEquiv.det gW.val * LinearEquiv.det gW.val = 1 := by
    rw [hdet_eq]
    exact huU
  have hW_eq : gW = scalarOnW (F := F) (LinearEquiv.det gU.val) huU := by
    calc gW = scalarOnW (F := F) (LinearEquiv.det gW.val) huW := eq_scalarOnW F gW huW
      _ = scalarOnW (F := F) (LinearEquiv.det gU.val) huU :=
          scalarOnW_congr (F := F) hdet_eq huW huU
  have hpos' : positiveOrthogonalExtension Q (zOp F) 1 one_ne_zero F.two_ne_zero
      (zOp_mul_self F) (zOp_selfAdjoint F)
        (scalarOnW (F := F) (LinearEquiv.det gU.val) huU, gU) = gO := by
    rw [← hW_eq]
    exact hpos
  rw [← hgU]
  unfold extendU
  dsimp only
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mk, Subtype.coe_mk, QuadraticMap.orthogonalDet_apply]
  rw [hpos']
  rfl

theorem restrictU_extendU (h : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) :
    restrictU F (extendU F h) = h := by
  unfold extendU
  dsimp only
  change (splitOrthogonalRestriction Q (zOp F) 1
    (positiveOrthogonalExtension Q (zOp F) 1 one_ne_zero F.two_ne_zero (zOp_mul_self F)
      (zOp_selfAdjoint F) (scalarOnW F _ _, h))).2 = h
  rw [splitOrthogonalRestriction_positive_extension]

@[expose] def centralizerEquiv : H F ≃* TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype) where
  toFun := restrictU F
  invFun := extendU F
  left_inv := extendU_restrictU F
  right_inv := restrictU_extendU F
  map_mul' := (restrictU F).map_mul

@[expose] def extendUHom : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype) →* H F :=
  (centralizerEquiv F).symm.toMonoidHom

theorem extendUHom_apply (h : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) :
    extendUHom F h = extendU F h := rfl

abbrev C0 : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  SO5 (Q := Q) ⊓ Subgroup.centralizer ({F.zO} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))

@[expose] def HtoC0 (g : H F) : C0 F where
  val := g.val.val
  property := ⟨g.val.property, by
    have h := congrArg (fun s : SO5 (Q := Q) => (s : TauCeti.QuadraticMap.orthogonalGroup Q))
      (Subgroup.mem_centralizer_singleton_iff.mp g.property)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa [FrameData.zSO, FrameData.zO] using h)⟩

def C0toH (x : C0 F) : H F where
  val := ⟨x.val, x.property.1⟩
  property := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.property.2

@[expose] def centralizerSubtypeEquiv : H F ≃* C0 F where
  toFun := HtoC0 F
  invFun := C0toH F
  left_inv := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl
  map_mul' := by
    intro g h
    rfl

theorem centralizerEquiv_apply (g : H F) :
    centralizerEquiv F g = restrictU F g := rfl

theorem centralizerEquiv_symm_apply (h : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) :
    (centralizerEquiv F).symm h = extendU F h := rfl


@[expose] def iota : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype) →*
    TauCeti.QuadraticMap.orthogonalGroup Q :=
  (SO5 (Q := Q)).subtype.comp ((H F).subtype.comp
    (centralizerEquiv F).symm.toMonoidHom)

theorem iota_apply (h : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) :
    iota F h = (extendU F h).val.val := rfl

theorem iota_mem_C0 (h : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) :
    iota F h ∈ C0 F := by
  have hmem := (HtoC0 F ((centralizerEquiv F).symm h)).property
  simpa [iota, HtoC0, centralizerEquiv_symm_apply] using hmem

def zFullCentralizerEquiv :
    orthogonalOperatorCentralizer Q (zOp F) ≃*
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (W F).subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) :=
  positiveOrthogonalCentralizerEquiv Q (zOp F) 1 one_ne_zero F.two_ne_zero
    (zOp_mul_self F) (zOp_selfAdjoint F)

end CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel

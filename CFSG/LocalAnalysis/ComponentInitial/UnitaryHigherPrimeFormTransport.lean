module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem barTranspose_mul_mul (h : UnitaryFieldData p f K) {ι κ μ : Type} [Fintype ι] [Fintype κ]
    (G : Matrix ι ι K) (A : Matrix ι κ K) (B : Matrix κ μ K) :
    ((A * B).map h.bar)ᵀ * G * (A * B) = (B.map h.bar)ᵀ * ((A.map h.bar)ᵀ * G * A) * B := by
  rw [Matrix.map_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

theorem map_barTranspose_mul_mul (h : UnitaryFieldData p f K) (φ : K ≃+* K) {ι κ : Type}
    [Fintype ι] (G : Matrix ι ι K) (W : Matrix ι κ K) :
    ((W.map φ).map h.bar)ᵀ * G.map φ * W.map φ = ((W.map h.bar)ᵀ * G * W).map φ := by
  rw [Matrix.map_mul, Matrix.map_mul, transpose_map]
  congr 3
  ext i j
  simp [map_bar_comm]

section Transport

variable (h : UnitaryFieldData p f K) (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)

@[expose] def IsGramHypTransport (W : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K) : Prop :=
  (W.map h.bar)ᵀ * C * W = hypGram r ε K

@[expose] noncomputable def gramHypInv (W : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (Fin (2 * r + ε)) K :=
  hypGram r ε K * (W.map h.bar)ᵀ * C

theorem exists_isGramHypTransport (hC : (C.map h.bar)ᵀ = C) (hdet : C.det ≠ 0) :
    ∃ W : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K, IsGramHypTransport h C W := by
  obtain ⟨w, hw⟩ := exists_hypBasis h (gramForm_isSymm h hC) (gramForm_separatingLeft h hdet)
    (r := r) (ε := ε) (Module.finrank_fin_fun K)
  refine ⟨Matrix.of fun k x => w x k, ?_⟩
  ext x y
  have h1 := gramForm_single h (((Matrix.of fun k x => w x k).map h.bar)ᵀ * C *
    Matrix.of fun k x => w x k) x y
  rw [← gramForm_mulVec, mulVec_single_one, mulVec_single_one] at h1
  rw [← h1, ← hw x y]
  rfl

variable {h C} {W : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}

theorem gramHypInv_mul (hW : IsGramHypTransport h C W) : gramHypInv h C W * W = 1 := by
  have hW' : (W.map h.bar)ᵀ * (C * W) = hypGram r ε K := by
    rw [← Matrix.mul_assoc]
    exact hW
  simp only [gramHypInv, Matrix.mul_assoc]
  rw [hW', hypGram_mul_self]

theorem mul_gramHypInv (hW : IsGramHypTransport h C W) : W * gramHypInv h C W = 1 := by
  set e : HypIndex r ε ≃ Fin (2 * r + ε) := Fintype.equivFinOfCardEq card_hypIndex
  have h1 : (gramHypInv h C W).submatrix e.symm (Equiv.refl _) *
      W.submatrix (Equiv.refl _) e.symm = 1 := by
    rw [submatrix_mul_equiv, gramHypInv_mul hW, submatrix_one_equiv]
  have h2 := mul_eq_one_comm.mp h1
  rw [submatrix_mul_equiv] at h2
  simpa using h2

theorem gramHypInv_gram (hW : IsGramHypTransport h C W) :
    ((gramHypInv h C W).map h.bar)ᵀ * hypGram r ε K * gramHypInv h C W = C := by
  have h1 := barTranspose_mul_mul h C W (gramHypInv h C W)
  rw [mul_gramHypInv hW, hW, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one,
    Matrix.one_mul, Matrix.mul_one] at h1
  exact h1.symm

theorem gramToHyp_mul_mul (hW : IsGramHypTransport h C W)
    (M N : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) :
    gramHypInv h C W * M * W * (gramHypInv h C W * N * W) = gramHypInv h C W * (M * N) * W := by
  rw [show gramHypInv h C W * M * W * (gramHypInv h C W * N * W) =
    gramHypInv h C W * M * (W * gramHypInv h C W) * N * W by simp only [Matrix.mul_assoc],
    mul_gramHypInv hW, Matrix.mul_one, Matrix.mul_assoc (gramHypInv h C W) M N]

theorem gramOfHyp_mul_mul (hW : IsGramHypTransport h C W)
    (M N : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    W * M * gramHypInv h C W * (W * N * gramHypInv h C W) = W * (M * N) * gramHypInv h C W := by
  rw [show W * M * gramHypInv h C W * (W * N * gramHypInv h C W) =
    W * M * (gramHypInv h C W * W) * N * gramHypInv h C W by simp only [Matrix.mul_assoc],
    gramHypInv_mul hW, Matrix.mul_one, Matrix.mul_assoc W M N]

theorem gramToHyp_one (hW : IsGramHypTransport h C W) :
    gramHypInv h C W * (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W = 1 := by
  rw [Matrix.mul_one, gramHypInv_mul hW]

theorem gramOfHyp_one (hW : IsGramHypTransport h C W) :
    W * (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) * gramHypInv h C W = 1 := by
  rw [Matrix.mul_one, mul_gramHypInv hW]

theorem gramOfHyp_gramToHyp (hW : IsGramHypTransport h C W)
    (M : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) :
    W * (gramHypInv h C W * M * W) * gramHypInv h C W = M := by
  rw [show W * (gramHypInv h C W * M * W) * gramHypInv h C W =
      (W * gramHypInv h C W) * M * (W * gramHypInv h C W) by simp only [Matrix.mul_assoc],
    mul_gramHypInv hW, Matrix.one_mul, Matrix.mul_one]

theorem gramToHyp_gramOfHyp (hW : IsGramHypTransport h C W)
    (N : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    gramHypInv h C W * (W * N * gramHypInv h C W) * W = N := by
  rw [show gramHypInv h C W * (W * N * gramHypInv h C W) * W =
      (gramHypInv h C W * W) * N * (gramHypInv h C W * W) by simp only [Matrix.mul_assoc],
    gramHypInv_mul hW, Matrix.one_mul, Matrix.mul_one]

theorem gramToHyp_scalar (hW : IsGramHypTransport h C W) (c : K) :
    gramHypInv h C W * Matrix.scalar (Fin (2 * r + ε)) c * W = Matrix.scalar (HypIndex r ε) c := by
  rw [scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    gramHypInv_mul hW, scalar_apply, ← smul_one_eq_diagonal]

theorem gramOfHyp_scalar (hW : IsGramHypTransport h C W) (c : K) :
    W * Matrix.scalar (HypIndex r ε) c * gramHypInv h C W = Matrix.scalar (Fin (2 * r + ε)) c := by
  rw [scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    mul_gramHypInv hW, scalar_apply, ← smul_one_eq_diagonal]

@[expose] noncomputable def gramToHypGL (hW : IsGramHypTransport h C W)
    (g : GL (Fin (2 * r + ε)) K) : GL (HypIndex r ε) K where
  val := gramHypInv h C W * (g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W
  inv := gramHypInv h C W *
    ((g⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W
  val_inv := by
    rw [gramToHyp_mul_mul hW, ← Units.val_mul, mul_inv_cancel, Units.val_one, gramToHyp_one hW]
  inv_val := by
    rw [gramToHyp_mul_mul hW, ← Units.val_mul, inv_mul_cancel, Units.val_one, gramToHyp_one hW]

@[expose] noncomputable def gramOfHypGL (hW : IsGramHypTransport h C W)
    (g : GL (HypIndex r ε) K) : GL (Fin (2 * r + ε)) K where
  val := W * (g : Matrix (HypIndex r ε) (HypIndex r ε) K) * gramHypInv h C W
  inv := W * ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
    gramHypInv h C W
  val_inv := by
    rw [gramOfHyp_mul_mul hW, ← Units.val_mul, mul_inv_cancel, Units.val_one, gramOfHyp_one hW]
  inv_val := by
    rw [gramOfHyp_mul_mul hW, ← Units.val_mul, inv_mul_cancel, Units.val_one, gramOfHyp_one hW]

theorem coe_gramToHypGL (hW : IsGramHypTransport h C W) (g : GL (Fin (2 * r + ε)) K) :
    ((gramToHypGL hW g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      gramHypInv h C W * (g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W :=
  rfl

theorem coe_gramOfHypGL (hW : IsGramHypTransport h C W) (g : GL (HypIndex r ε) K) :
    ((gramOfHypGL hW g : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
      W * (g : Matrix (HypIndex r ε) (HypIndex r ε) K) * gramHypInv h C W :=
  rfl

theorem gramToHypGL_mem (hW : IsGramHypTransport h C W) {g : GL (Fin (2 * r + ε)) K}
    (hg : g ∈ gramSU h C) : gramToHypGL hW g ∈ hypSU h r ε := by
  refine mem_hypSU.mpr ⟨?_, ?_⟩
  · rw [coe_gramToHypGL, barTranspose_mul_mul, barTranspose_mul_mul, gramHypInv_gram hW, hg.1, hW]
  · rw [coe_gramToHypGL, det_mul_mul_of_mul_eq_one (Fintype.equivFinOfCardEq card_hypIndex).symm
      (gramHypInv_mul hW)]
    exact hg.2

theorem gramOfHypGL_mem (hW : IsGramHypTransport h C W) {g : GL (HypIndex r ε) K}
    (hg : g ∈ hypSU h r ε) : gramOfHypGL hW g ∈ gramSU h C := by
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · rw [coe_gramOfHypGL, barTranspose_mul_mul, barTranspose_mul_mul, hW, hg.1, gramHypInv_gram hW]
  · rw [coe_gramOfHypGL, det_mul_mul_of_mul_eq_one (Fintype.equivFinOfCardEq card_hypIndex)
      (mul_gramHypInv hW)]
    exact hg.2

variable (h C) in
@[expose] noncomputable def gramHypEquiv (hW : IsGramHypTransport h C W) :
    gramSU h C ≃* hypSU h r ε where
  toFun g := ⟨gramToHypGL hW g, gramToHypGL_mem hW g.2⟩
  invFun g := ⟨gramOfHypGL hW g, gramOfHypGL_mem hW g.2⟩
  left_inv _ := Subtype.ext (Units.ext (gramOfHyp_gramToHyp hW _))
  right_inv _ := Subtype.ext (Units.ext (gramToHyp_gramOfHyp hW _))
  map_mul' _ _ := Subtype.ext (Units.ext (gramToHyp_mul_mul hW _ _).symm)

theorem coe_gramHypEquiv (hW : IsGramHypTransport h C W) (g : gramSU h C) :
    (((gramHypEquiv h C hW g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
        gramHypInv h C W * ((g : GL (Fin (2 * r + ε)) K) :
          Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W :=
  rfl

theorem mem_normOneScalars_iff_gramHyp (hW : IsGramHypTransport h C W) (g : gramSU h C) :
    g ∈ normOneScalars h (gramSU h C) (2 * r + ε) ↔ gramHypEquiv h C hW g ∈ hypScalars h r ε := by
  constructor
  · rintro ⟨c, hc, hcn, hg⟩
    refine ⟨c, hc, hcn, Units.ext ?_⟩
    rw [coe_gramHypEquiv, hg, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
      gramToHyp_scalar hW]
  · rintro ⟨c, hc, hcn, hg⟩
    refine ⟨c, hc, hcn, Units.ext ?_⟩
    have hg' : gramHypInv h C W * ((g : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W =
          Matrix.scalar (HypIndex r ε) (c : K) := by
      rw [← coe_gramHypEquiv hW g, hg, GeneralLinearGroup.coe_scalar]
    rw [GeneralLinearGroup.coe_scalar, ← gramOfHyp_gramToHyp hW ((g : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K), hg', gramOfHyp_scalar hW]

theorem map_normOneScalars_gramHypEquiv (hW : IsGramHypTransport h C W) :
    (normOneScalars h (gramSU h C) (2 * r + ε)).map (gramHypEquiv h C hW).toMonoidHom =
      hypScalars h r ε := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_normOneScalars_iff_gramHyp hW g).mp hg
  · intro hx
    refine ⟨(gramHypEquiv h C hW).symm x, (mem_normOneScalars_iff_gramHyp hW _).mpr ?_,
      MulEquiv.apply_symm_apply _ _⟩
    rwa [MulEquiv.apply_symm_apply]

variable (h C) in
@[expose] noncomputable def gramHypProjEquiv (hW : IsGramHypTransport h C W) :
    primeFormP h C ≃* hypPSU h r ε :=
  QuotientGroup.congr _ _ (gramHypEquiv h C hW) (map_normOneScalars_gramHypEquiv hW)

theorem gramHypProjEquiv_mk (hW : IsGramHypTransport h C W) (g : gramSU h C) :
    gramHypProjEquiv h C hW (g : primeFormP h C) =
      ((gramHypEquiv h C hW g : hypSU h r ε) : hypPSU h r ε) :=
  QuotientGroup.congr_mk _ _ _ _ g

end Transport

section Semilinear

variable {h : UnitaryFieldData p f K} {C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K}
  {W : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}

theorem map_mul_gramHypInv (hW : IsGramHypTransport h C W) (φ : K ≃+* K) :
    W.map φ * (gramHypInv h C W).map φ = 1 := by
  rw [← Matrix.map_mul, mul_gramHypInv hW, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem map_gramHypInv_mul (hW : IsGramHypTransport h C W) (φ : K ≃+* K) :
    (gramHypInv h C W).map φ * W.map φ = 1 := by
  rw [← Matrix.map_mul, gramHypInv_mul hW, Matrix.map_one _ (map_zero φ) (map_one φ)]

@[expose] noncomputable def gramToHypSemiGL (hW : IsGramHypTransport h C W)
    (A : GL (Fin (2 * r + ε)) K) (φ : K ≃+* K) : GL (HypIndex r ε) K where
  val := gramHypInv h C W * (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W.map φ
  inv := (gramHypInv h C W).map φ *
    ((A⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W
  val_inv := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (W.map φ), map_mul_gramHypInv hW, Matrix.one_mul,
      ← Matrix.mul_assoc (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K), Units.mul_inv,
      Matrix.one_mul, gramHypInv_mul hW]
  inv_val := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W, mul_gramHypInv hW, Matrix.one_mul,
      ← Matrix.mul_assoc ((A⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε))
        (Fin (2 * r + ε)) K), Units.inv_mul, Matrix.one_mul, map_gramHypInv_mul hW]

@[expose] noncomputable def gramOfHypSemiGL (hW : IsGramHypTransport h C W)
    (B : GL (HypIndex r ε) K) (σ : K ≃+* K) : GL (Fin (2 * r + ε)) K where
  val := W * (B : Matrix (HypIndex r ε) (HypIndex r ε) K) * (gramHypInv h C W).map σ
  inv := W.map σ * ((B⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
    gramHypInv h C W
  val_inv := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((gramHypInv h C W).map σ), map_gramHypInv_mul hW, Matrix.one_mul,
      ← Matrix.mul_assoc (B : Matrix (HypIndex r ε) (HypIndex r ε) K), Units.mul_inv,
      Matrix.one_mul, mul_gramHypInv hW]
  inv_val := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (gramHypInv h C W), gramHypInv_mul hW, Matrix.one_mul,
      ← Matrix.mul_assoc ((B⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K),
      Units.inv_mul, Matrix.one_mul, map_mul_gramHypInv hW]

theorem coe_gramToHypSemiGL (hW : IsGramHypTransport h C W) (A : GL (Fin (2 * r + ε)) K)
    (φ : K ≃+* K) :
    ((gramToHypSemiGL hW A φ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      gramHypInv h C W * (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W.map φ :=
  rfl

theorem coe_gramOfHypSemiGL (hW : IsGramHypTransport h C W) (B : GL (HypIndex r ε) K)
    (σ : K ≃+* K) :
    ((gramOfHypSemiGL hW B σ : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
        W * (B : Matrix (HypIndex r ε) (HypIndex r ε) K) * (gramHypInv h C W).map σ :=
  rfl

theorem gramToHyp_gramOfHypSemi (hW : IsGramHypTransport h C W) (B : GL (HypIndex r ε) K)
    (σ : K ≃+* K) :
    gramHypInv h C W * ((gramOfHypSemiGL hW B σ : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W.map σ = B := by
  rw [coe_gramOfHypSemiGL]
  simp only [Matrix.mul_assoc]
  rw [map_gramHypInv_mul hW, Matrix.mul_one, ← Matrix.mul_assoc, gramHypInv_mul hW,
    Matrix.one_mul]

variable (hCφ : ∀ φ : K ≃+* K, C.map φ = C)

include hCφ

theorem gramToHypSemiGL_mem (hW : IsGramHypTransport h C W) {A : GL (Fin (2 * r + ε)) K}
    (hA : A ∈ primeFormUnitary h C) (φ : K ≃+* K) :
    gramToHypSemiGL hW A φ ∈ hypUnitary h r ε := by
  rw [mem_hypUnitary, coe_gramToHypSemiGL, barTranspose_mul_mul, barTranspose_mul_mul,
    gramHypInv_gram hW, mem_primeFormUnitary.mp hA, ← hCφ φ, map_barTranspose_mul_mul, hW,
    hypGram_map_ringEquiv]

theorem gramOfHypSemiGL_mem (hW : IsGramHypTransport h C W) {B : GL (HypIndex r ε) K}
    (hB : B ∈ hypUnitary h r ε) (σ : K ≃+* K) :
    gramOfHypSemiGL hW B σ ∈ primeFormUnitary h C := by
  rw [mem_primeFormUnitary, coe_gramOfHypSemiGL, barTranspose_mul_mul, barTranspose_mul_mul, hW,
    mem_hypUnitary.mp hB, ← hypGram_map_ringEquiv σ, map_barTranspose_mul_mul,
    gramHypInv_gram hW, hCφ σ]

end Semilinear

theorem gramHyp_conj_eq {h : UnitaryFieldData p f K}
    {C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K}
    {W : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}
    (hW : IsGramHypTransport h C W) {A : GL (Fin (2 * r + ε)) K} {φ : K ≃+* K}
    {B : GL (HypIndex r ε) K}
    (hB : (B : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      gramHypInv h C W * (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W.map φ)
    (g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) :
    (B : Matrix (HypIndex r ε) (HypIndex r ε) K) * (gramHypInv h C W * g * W).map φ *
      ((B⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        gramHypInv h C W * ((A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * g.map φ *
          ((A⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)) * W := by
  have hBeq : B = gramToHypSemiGL hW A φ := Units.ext hB
  have hBinv : ((B⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (gramHypInv h C W).map φ *
        ((A⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W := by
    rw [hBeq]
    rfl
  have hcancel : ∀ X : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K,
      W.map φ * ((gramHypInv h C W).map φ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, map_mul_gramHypInv hW, Matrix.one_mul]
  rw [hBinv, hB, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc, hcancel]

section Psi

variable {h : UnitaryFieldData p f K} {C : GL (Fin (2 * r + ε)) K} (hC : IsPrimeFormGram C)
  {W : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}

theorem gramHypProjEquiv_psi
    (hW : IsGramHypTransport h (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) W)
    (hr : 1 ≤ r) (hε : ε ≤ 1) (A : primeFormUnitary h (C : Matrix (Fin (2 * r + ε))
      (Fin (2 * r + ε)) K)) (x : semilinearSimilitudes h r ε)
    (hx : (((x : SemiGL (HypIndex r ε) K).left : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
        gramHypInv h (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) W *
          ((A : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *
            W.map (x : SemiGL (HypIndex r ε) K).right)
    (y : primeFormP h (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)) :
    gramHypProjEquiv h _ hW (primeFormPsi h hC ⟨A, (x : SemiGL (HypIndex r ε) K).right⟩ y) =
      semilinearAutHom h hr hε x (gramHypProjEquiv h _ hW y) := by
  refine QuotientGroup.induction_on y fun g => ?_
  rw [primeFormPsi_apply, MulAut.mul_apply]
  change gramHypProjEquiv h _ hW (primeFormConjHom h _ A
    (primeFormFieldAut h hC _ (g : primeFormP h _))) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk, gramHypProjEquiv_mk, gramHypProjEquiv_mk]
  change _ = semilinearAutHom h hr hε x (hypProj h r ε _)
  rw [semilinearAutHom_apply]
  change ((_ : hypSU h r ε) : hypPSU h r ε) = ((_ : hypSU h r ε) : hypPSU h r ε)
  congr 1
  refine Subtype.ext (Units.ext ?_)
  rw [coe_gramHypEquiv]
  change gramHypInv h (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) W *
      (((A : GL (Fin (2 * r + ε)) K) * glAut (x : SemiGL (HypIndex r ε) K).right
        (g : GL (Fin (2 * r + ε)) K) * (A : GL (Fin (2 * r + ε)) K)⁻¹ : GL (Fin (2 * r + ε)) K) :
          Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * W =
    (((x : SemiGL (HypIndex r ε) K).left * glAut (x : SemiGL (HypIndex r ε) K).right
      (gramToHypGL hW (g : GL (Fin (2 * r + ε)) K)) * (x : SemiGL (HypIndex r ε) K).left⁻¹ :
        GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, coe_glAut, coe_glAut,
    coe_gramToHypGL]
  exact (gramHyp_conj_eq hW hx _).symm

end Psi

theorem lineNormalizer_eq_semilinearPointGroup_of_admissible (h : UnitaryFieldData p f K)
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (hq : ¬(2 * r + ε = 3 ∧ p ^ f = 2)) :
    lineNormalizer h r ε = semilinearPointGroup h r ε := by
  rcases (by omega : r = 1 ∨ r = 2 ∨ 3 ≤ r) with rfl | rfl | hr3
  · obtain rfl : ε = 1 := by omega
    have hq2 : 2 < p ^ f := by
      have h1 := h.one_lt_pow
      have h2 : p ^ f ≠ 2 := fun h2 => hq ⟨by omega, h2⟩
      omega
    exact (unitary_rank_one_permutation_normalizer h hq2).1
  · exact (unitary_rank_two_permutation_normalizer h hε).1
  · exact (unitary_higher_permutation_normalizer h hr3 hε).1

theorem semilinearAutHom_surjective_of_admissible (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (hq : ¬(2 * r + ε = 3 ∧ p ^ f = 2)) :
    Function.Surjective (semilinearAutHom h hr hε) := by
  intro α
  have hmem : linePerm h hr hε α ∈ semilinearPointGroup h r ε := by
    rw [← lineNormalizer_eq_semilinearPointGroup_of_admissible h hr hε hn hq,
      ← range_linePerm h hr hε]
    exact ⟨α, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, linePerm_injective h hr hε ?_⟩
  rw [linePerm_semilinearAutHom, hx]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

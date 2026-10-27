module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionCharacter

public section

namespace CFSG.ComponentClassification.CatalogueBGraphForm

noncomputable section

universe u

@[expose] def glTranspose (n : ℕ) (K : Type u) [Field K]
    (g : Matrix.GeneralLinearGroup (Fin n) K) : Matrix.GeneralLinearGroup (Fin n) K :=
  (glGraphAut n K g)⁻¹

theorem glTranspose_matrix (n : ℕ) (K : Type u) [Field K]
    (g : Matrix.GeneralLinearGroup (Fin n) K) :
    (glTranspose n K g).val = g.val.transpose := by
  rw [glTranspose, ← map_inv, glGraphAut_matrix, inv_inv]

theorem glTranspose_mul (n : ℕ) (K : Type u) [Field K]
    (g h : Matrix.GeneralLinearGroup (Fin n) K) :
    glTranspose n K (g * h) = glTranspose n K h * glTranspose n K g := by
  simp only [glTranspose, map_mul, mul_inv_rev]

theorem glTranspose_inv (n : ℕ) (K : Type u) [Field K]
    (g : Matrix.GeneralLinearGroup (Fin n) K) :
    glTranspose n K g⁻¹ = (glTranspose n K g)⁻¹ := by
  simp only [glTranspose, map_inv, inv_inv]

theorem glTranspose_scalar (n : ℕ) (K : Type u) [Field K] (c : Kˣ) :
    glTranspose n K (Matrix.GeneralLinearGroup.scalar (Fin n) c) =
      Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  rw [glTranspose, glGraphAut_scalar, ← map_inv, inv_inv]

theorem scalar_mul_matrix (n : ℕ) (K : Type u) [Field K] (c : Kˣ)
    (M : Matrix (Fin n) (Fin n) K) :
    (Matrix.GeneralLinearGroup.scalar (Fin n) c).val * M = c.val • M := by
  have hs : (Matrix.GeneralLinearGroup.scalar (Fin n) c).val =
      c.val • (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
  rw [hs, Matrix.smul_mul, Matrix.one_mul]

theorem similitude_mul_equation (n : ℕ) (K : Type u) [Field K]
    (R g h : Matrix.GeneralLinearGroup (Fin n) K) (mu nu : Kˣ)
    (hg : glTranspose n K g * R * g = R * Matrix.GeneralLinearGroup.scalar (Fin n) mu)
    (hh : glTranspose n K h * R * h = R * Matrix.GeneralLinearGroup.scalar (Fin n) nu) :
    glTranspose n K (g * h) * R * (g * h) =
      R * Matrix.GeneralLinearGroup.scalar (Fin n) (mu * nu) := by
  rw [glTranspose_mul]
  calc
    _ = glTranspose n K h * (glTranspose n K g * R * g) * h := by group
    _ = glTranspose n K h * (R * Matrix.GeneralLinearGroup.scalar (Fin n) mu) * h := by rw [hg]
    _ = (glTranspose n K h * R * h) * Matrix.GeneralLinearGroup.scalar (Fin n) mu := by
      simp only [mul_assoc]
      rw [Matrix.GeneralLinearGroup.scalar_commute]
    _ = (R * Matrix.GeneralLinearGroup.scalar (Fin n) nu) *
        Matrix.GeneralLinearGroup.scalar (Fin n) mu := by rw [hh]
    _ = R * Matrix.GeneralLinearGroup.scalar (Fin n) (mu * nu) := by
      rw [mul_assoc, ← map_mul, mul_comm nu mu]

theorem similitude_inv_equation (n : ℕ) (K : Type u) [Field K]
    (R g : Matrix.GeneralLinearGroup (Fin n) K) (mu : Kˣ)
    (hg : glTranspose n K g * R * g = R * Matrix.GeneralLinearGroup.scalar (Fin n) mu) :
    glTranspose n K g⁻¹ * R * g⁻¹ = R * Matrix.GeneralLinearGroup.scalar (Fin n) mu⁻¹ := by
  have hcancel : (glTranspose n K g⁻¹ * R * g⁻¹) *
      Matrix.GeneralLinearGroup.scalar (Fin n) mu = R := by
    calc
      _ = glTranspose n K g⁻¹ * (R * Matrix.GeneralLinearGroup.scalar (Fin n) mu) * g⁻¹ := by
        simp only [mul_assoc]
        rw [Matrix.GeneralLinearGroup.scalar_commute]
      _ = glTranspose n K g⁻¹ * (glTranspose n K g * R * g) * g⁻¹ := by rw [hg]
      _ = R := by rw [glTranspose_inv]; group
  rw [map_inv]
  exact eq_mul_inv_iff_mul_eq.mpr hcancel

@[expose] def isometryGroup (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) : Subgroup (Matrix.GeneralLinearGroup (Fin n) K) where
  carrier := {g | glTranspose n K g * R * g = R}
  one_mem' := by simp [glTranspose]
  mul_mem' {g h} hg hh := by
    change glTranspose n K (g * h) * R * (g * h) = R
    simpa only [map_one, mul_one] using
      similitude_mul_equation n K R g h 1 1 (by simpa using hg) (by simpa using hh)
  inv_mem' {g} hg := by
    change glTranspose n K g⁻¹ * R * g⁻¹ = R
    simpa only [inv_one, map_one, mul_one] using
      similitude_inv_equation n K R g 1 (by simpa using hg)

theorem mem_isometryGroup (n : ℕ) (K : Type u) [Field K]
    (R g : Matrix.GeneralLinearGroup (Fin n) K) :
    g ∈ isometryGroup n K R ↔ g.val.transpose * R.val * g.val = R.val := by
  change glTranspose n K g * R * g = R ↔ _
  rw [← Units.val_inj, Units.val_mul, Units.val_mul, glTranspose_matrix]

@[expose] def similitudeGroup (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) : Subgroup (Matrix.GeneralLinearGroup (Fin n) K) where
  carrier := {g | ∃ mu : Kˣ,
    glTranspose n K g * R * g = R * Matrix.GeneralLinearGroup.scalar (Fin n) mu}
  one_mem' := ⟨1, by simp [glTranspose]⟩
  mul_mem' {g h} hg hh := by
    obtain ⟨mu, hmu⟩ := hg
    obtain ⟨nu, hnu⟩ := hh
    exact ⟨mu * nu, similitude_mul_equation n K R g h mu nu hmu hnu⟩
  inv_mem' {g} hg := by
    obtain ⟨mu, hmu⟩ := hg
    exact ⟨mu⁻¹, similitude_inv_equation n K R g mu hmu⟩

theorem mem_similitudeGroup (n : ℕ) (K : Type u) [Field K]
    (R g : Matrix.GeneralLinearGroup (Fin n) K) :
    g ∈ similitudeGroup n K R ↔ ∃ mu : Kˣ,
      g.val.transpose * R.val * g.val = mu.val • R.val := by
  change (∃ mu : Kˣ, glTranspose n K g * R * g =
    R * Matrix.GeneralLinearGroup.scalar (Fin n) mu) ↔ _
  apply exists_congr
  intro mu
  rw [← Units.val_inj, Units.val_mul, Units.val_mul, glTranspose_matrix,
    ← Matrix.GeneralLinearGroup.scalar_commute, Units.val_mul, scalar_mul_matrix]

theorem isometry_le_similitude (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) :
    isometryGroup n K R ≤ similitudeGroup n K R := by
  intro g hg
  change glTranspose n K g * R * g = R at hg
  exact ⟨1, by simpa using hg⟩

@[expose] def similitudeMultiplier (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (g : similitudeGroup n K R) : Kˣ :=
  g.property.choose

theorem similitudeMultiplier_spec (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (g : similitudeGroup n K R) :
    glTranspose n K g.val * R * g.val =
      R * Matrix.GeneralLinearGroup.scalar (Fin n) (similitudeMultiplier n K R g) :=
  g.property.choose_spec

theorem similitudeMultiplier_matrix (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (g : similitudeGroup n K R) :
    g.val.val.transpose * R.val * g.val.val =
      (similitudeMultiplier n K R g).val • R.val := by
  have h := congrArg Units.val (similitudeMultiplier_spec n K R g)
  rw [Units.val_mul, Units.val_mul, glTranspose_matrix,
    ← Matrix.GeneralLinearGroup.scalar_commute, Units.val_mul, scalar_mul_matrix] at h
  exact h

theorem similitudeMultiplier_unique (n : ℕ) (K : Type u) [Field K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (g : similitudeGroup n K R) (mu : Kˣ)
    (hmu : glTranspose n K g.val * R * g.val = R * Matrix.GeneralLinearGroup.scalar (Fin n) mu) :
    similitudeMultiplier n K R g = mu :=
  CatalogueBProjectiveInvolution.scalarGL_injective
    (mul_left_cancel ((similitudeMultiplier_spec n K R g).symm.trans hmu))

theorem similitudeMultiplier_unique_matrix
    (n : ℕ) (K : Type u) [Field K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (g : similitudeGroup n K R) (mu : Kˣ)
    (hmu : g.val.val.transpose * R.val * g.val.val = mu.val • R.val) :
    similitudeMultiplier n K R g = mu := by
  apply similitudeMultiplier_unique n K R g mu
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, glTranspose_matrix,
    ← Matrix.GeneralLinearGroup.scalar_commute, Units.val_mul, scalar_mul_matrix]
  exact hmu

@[expose] def similitudeMultiplierHom (n : ℕ) (K : Type u) [Field K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) : similitudeGroup n K R →* Kˣ where
  toFun := similitudeMultiplier n K R
  map_one' := similitudeMultiplier_unique n K R 1 1 (by simp [glTranspose])
  map_mul' g h := similitudeMultiplier_unique n K R (g * h)
    (similitudeMultiplier n K R g * similitudeMultiplier n K R h)
    (similitude_mul_equation n K R g.val h.val _ _
      (similitudeMultiplier_spec n K R g) (similitudeMultiplier_spec n K R h))

abbrev isometryInSimilitude (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) : Subgroup (similitudeGroup n K R) :=
  (isometryGroup n K R).subgroupOf (similitudeGroup n K R)

theorem similitudeMultiplier_kernel (n : ℕ) (K : Type u) [Field K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) :
    (similitudeMultiplierHom n K R).ker = isometryInSimilitude n K R := by
  ext g
  change similitudeMultiplier n K R g = 1 ↔ glTranspose n K g.val * R * g.val = R
  constructor
  · intro h
    simpa only [h, map_one, mul_one] using similitudeMultiplier_spec n K R g
  · intro h
    exact similitudeMultiplier_unique n K R g 1 (by simpa using h)

instance isometryInSimilitudeNormal (n : ℕ) (K : Type u) [Field K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) : (isometryInSimilitude n K R).Normal := by
  rw [← similitudeMultiplier_kernel]
  infer_instance

@[expose] def similitudeQuotientEquivMultiplierRange
    (n : ℕ) (K : Type u) [Field K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) :
    (similitudeGroup n K R ⧸ isometryInSimilitude n K R) ≃*
      (similitudeMultiplierHom n K R).range :=
  (QuotientGroup.quotientMulEquivOfEq (similitudeMultiplier_kernel n K R).symm).trans
    (QuotientGroup.quotientKerEquivRange (similitudeMultiplierHom n K R))

instance similitudeQuotientAbelian (n : ℕ) (K : Type u) [Field K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) :
    IsMulCommutative (similitudeGroup n K R ⧸ isometryInSimilitude n K R) := by
  let e := similitudeQuotientEquivMultiplierRange n K R
  refine ⟨⟨fun x y => e.injective ?_⟩⟩
  rw [map_mul, map_mul, mul_comm]

instance similitudeQuotientSolvable (n : ℕ) (K : Type u) [Field K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) :
    Group.IsSolvable (similitudeGroup n K R ⧸ isometryInSimilitude n K R) :=
  Group.isSolvable_of_isSolvable_injective
    (f := (similitudeQuotientEquivMultiplierRange n K R).toMonoidHom)
    (similitudeQuotientEquivMultiplierRange n K R).injective

@[expose] def isometryInSimilitudeEquiv (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) :
    isometryInSimilitude n K R ≃* isometryGroup n K R :=
  Subgroup.subgroupOfEquivOfLe (isometry_le_similitude n K R)

theorem isometryInSimilitudeEquiv_val (n : ℕ) (K : Type u) [Field K]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (g : isometryInSimilitude n K R) :
    (isometryInSimilitudeEquiv n K R g).val = g.val.val := rfl

end

end CFSG.ComponentClassification.CatalogueBGraphForm

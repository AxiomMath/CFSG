module

public import CFSG.LieType.SteinbergBRUnitaryPlaneMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometrySpaces

public noncomputable section

namespace CFSG.LieType.SteinbergBR

open Matrix CFSG.ComponentClassification.CatalogueBUnitaryTwo
  CFSG.ComponentClassification.CatalogueBLinearTwoDescent CFSG.LieType.Universal.Unitary
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry
open scoped MatrixGroups

universe u v

variable {E : Type u} [Field E] {V : Type v} [AddCommGroup V] [Module E V]

@[expose] def coordMat (B : (Fin 2 → E) ≃ₗ[E] V) (g : V ≃ₗ[E] V) : Matrix (Fin 2) (Fin 2) E :=
  LinearMap.toMatrix' ((B.trans g).trans B.symm).toLinearMap

theorem coordMat_mulVec (B : (Fin 2 → E) ≃ₗ[E] V) (g : V ≃ₗ[E] V) (x : Fin 2 → E) :
    coordMat B g *ᵥ x = B.symm (g (B x)) :=
  LinearMap.toMatrix'_mulVec _ x

theorem coordMat_mul (B : (Fin 2 → E) ≃ₗ[E] V) (g₁ g₂ : V ≃ₗ[E] V) :
    coordMat B (g₁ * g₂) = coordMat B g₁ * coordMat B g₂ := by
  rw [coordMat, coordMat, coordMat, ← LinearMap.toMatrix'_comp]
  congr 1
  refine LinearMap.ext fun x => ?_
  simp

theorem coordMat_one (B : (Fin 2 → E) ≃ₗ[E] V) : coordMat B 1 = 1 := by
  rw [coordMat, ← LinearMap.toMatrix'_id]
  congr 1
  refine LinearMap.ext fun x => ?_
  simp

theorem det_coordMat_ne_zero (B : (Fin 2 → E) ≃ₗ[E] V) (g : V ≃ₗ[E] V) :
    (coordMat B g).det ≠ 0 := by
  have h := congrArg Matrix.det (coordMat_mul B g⁻¹ g)
  rw [inv_mul_cancel, coordMat_one, det_one, det_mul] at h
  exact right_ne_zero_of_mul (h ▸ one_ne_zero)

@[expose] def conjCoord (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ) (g : V ≃ₗ[E] V) :
    Matrix (Fin 2) (Fin 2) E :=
  (diagonalGL t)⁻¹.val * coordMat B g * (diagonalGL t).val

theorem conjCoord_mul (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ) (g₁ g₂ : V ≃ₗ[E] V) :
    conjCoord B t (g₁ * g₂) = conjCoord B t g₁ * conjCoord B t g₂ := by
  have hD : (diagonalGL t).val * (diagonalGL t)⁻¹.val = 1 := (diagonalGL t).val_inv
  rw [conjCoord, conjCoord, conjCoord, coordMat_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonalGL t).val, hD, Matrix.one_mul]

theorem conjCoord_one (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ) : conjCoord B t 1 = 1 := by
  rw [conjCoord, coordMat_one, Matrix.mul_one]
  exact (diagonalGL t).inv_val

theorem conjCoord_eq (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ) (g : V ≃ₗ[E] V) :
    conjCoord B t g = conjugatedMatrix t (coordMat B g) := by
  rw [conjCoord]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugatedMatrix, diagonalGL, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, div_eq_mul_inv, mul_comm]

variable (σ : E ≃+* E)

@[expose] def fixedToE (A : Matrix (Fin 2) (Fin 2) (fixedSubfield E σ)) :
    Matrix (Fin 2) (Fin 2) E :=
  A.map fun x => (x : E)

theorem fixedToE_mul (A A' : Matrix (Fin 2) (Fin 2) (fixedSubfield E σ)) :
    fixedToE σ (A * A') = fixedToE σ A * fixedToE σ A' := by
  ext i j
  simp [fixedToE, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def IsRep (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ) (g : V ≃ₗ[E] V)
    (A₀ : GL (Fin 2) (fixedSubfield E σ)) : Prop :=
  ∃ c : Eˣ, conjCoord B t g = (c : E) • fixedToE σ (A₀ : Matrix (Fin 2) (Fin 2) _)

variable {σ}

theorem IsRep.mul {B : (Fin 2 → E) ≃ₗ[E] V} {t : Eˣ} {g₁ g₂ : V ≃ₗ[E] V}
    {A₁ A₂ : GL (Fin 2) (fixedSubfield E σ)} (h₁ : IsRep σ B t g₁ A₁) (h₂ : IsRep σ B t g₂ A₂) :
    IsRep σ B t (g₁ * g₂) (A₁ * A₂) := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  refine ⟨c₁ * c₂, ?_⟩
  rw [conjCoord_mul, hc₁, hc₂, Units.val_mul, Units.val_mul, fixedToE_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]

theorem IsRep.mk_eq {B : (Fin 2 → E) ≃ₗ[E] V} {t : Eˣ} {g : V ≃ₗ[E] V}
    {A₁ A₂ : GL (Fin 2) (fixedSubfield E σ)} (h₁ : IsRep σ B t g A₁) (h₂ : IsRep σ B t g A₂) :
    ProjGenLinGroup.mk A₁ = ProjGenLinGroup.mk A₂ := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  set M₁ : Matrix (Fin 2) (Fin 2) (fixedSubfield E σ) := A₁.val with hM₁
  set M₂ : Matrix (Fin 2) (Fin 2) (fixedSubfield E σ) := A₂.val with hM₂
  have he : (c₁ : E) • fixedToE σ M₁ = (c₂ : E) • fixedToE σ M₂ := hc₁.symm.trans hc₂
  obtain ⟨i, j, hij⟩ : ∃ i j, M₁ i j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply Matrix.GeneralLinearGroup.det_ne_zero A₁
    have : M₁ = 0 := Matrix.ext hall
    change M₁.det = 0
    rw [this, det_zero]
  set u : E := (c₁ : E) / c₂ with hu
  have hentry : ∀ k l, u * (M₁ k l : E) = (M₂ k l : E) := by
    intro k l
    have := congrFun₂ he k l
    simp only [fixedToE, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    rw [hu, div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ c₂.ne_zero]
  have hij' : (M₁ i j : E) ≠ 0 := fun h0 => hij (Subtype.ext h0)
  have huF : u ∈ fixedSubfield E σ := by
    have hu' : u = (M₂ i j : E) / (M₁ i j : E) := by
      rw [← hentry, mul_div_cancel_right₀ _ hij']
    rw [hu']
    exact div_mem (Subtype.prop _) (Subtype.prop _)
  have hu0 : u ≠ 0 := div_ne_zero c₁.ne_zero c₂.ne_zero
  have hu0' : (⟨u, huF⟩ : fixedSubfield E σ) ≠ 0 := fun h0 => hu0 (congrArg Subtype.val h0)
  rw [ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 ⟨u, huF⟩ hu0', Units.ext ?_⟩
  ext k l
  rw [← hentry k l]
  fin_cases k <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hM₁, mul_comm]

theorem isRep_one (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ) : IsRep σ B t 1 1 :=
  ⟨1, by
    rw [conjCoord_one, Units.val_one, one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fixedToE]⟩

variable {h : V →ₛₗ[σ.toRingHom] V →ₗ[E] E}

theorem coordMat_isometry {B : (Fin 2 → E) ≃ₗ[E] V}
    (hB : ∀ x y, h (B x) (B y) = hyperbolicForm σ x y) {g : V ≃ₗ[E] V}
    (hg : g ∈ isometryGroup h) :
    conjTr σ (coordMat B g) * hyperbolicMatrix * coordMat B g = hyperbolicMatrix := by
  rw [← hyperbolic_isometry_iff_matrix]
  intro x y
  rw [coordMat_mulVec, coordMat_mulVec, ← hB, ← hB, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact hg (B x) (B y)

theorem sigma_det_mul_det {A : Matrix (Fin 2) (Fin 2) E}
    (hA : conjTr σ A * hyperbolicMatrix * A = hyperbolicMatrix) (hdet : A.det ≠ 0) :
    σ A.det * A.det = 1 := by
  obtain ⟨h00, h11, h01, h10⟩ := hyperbolic_entries σ hA
  have e : σ A.det * A.det * A.det = A.det := by
    have hd : σ A.det = σ (A 0 0) * σ (A 1 1) - σ (A 0 1) * σ (A 1 0) := by
      rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
    calc σ A.det * A.det * A.det =
        σ (A 0 0) * A.det * (σ (A 1 1) * A.det) - σ (A 0 1) * A.det * (σ (A 1 0) * A.det) := by
          rw [hd]
          ring
      _ = A.det := by
          rw [h00, h11, h01, h10, Matrix.det_fin_two A]
          ring
  exact mul_right_cancel₀ hdet (by rw [e, one_mul])

theorem exists_isRep {t : Eˣ} (ht : σ (t : E) = -(t : E)) {B : (Fin 2 → E) ≃ₗ[E] V}
    {g : V ≃ₗ[E] V}
    (hA : conjTr σ (coordMat B g) * hyperbolicMatrix * coordMat B g = hyperbolicMatrix)
    (h90 : ∀ u : E, σ u * u = 1 → ∃ c : E, c ≠ 0 ∧ σ c * u = c) :
    ∃ A₀ : GL (Fin 2) (fixedSubfield E σ), IsRep σ B t g A₀ := by
  set A := coordMat B g with hAdef
  have hdet := det_coordMat_ne_zero B g
  obtain ⟨c, hc0, hc⟩ := h90 A.det (sigma_det_mul_det hA hdet)
  have hfix := fixed_conj_of_isometry hA ht hc0 hc
  let M : Matrix (Fin 2) (Fin 2) (fixedSubfield E σ) := fun i j =>
    ⟨(c⁻¹ • conjugatedMatrix t A) i j, (mem_fixedSubfield E σ _).2 (hfix i j)⟩
  have hME : fixedToE σ M = c⁻¹ • conjugatedMatrix t A := rfl
  have hMdet : M.det ≠ 0 := by
    intro h0
    have h1 : (fixedToE σ M).det = 0 := by
      have e := ((fixedSubfield E σ).subtype.map_det M).symm
      change (fixedToE σ M).det = _ at e
      rw [e, h0, map_zero]
    rw [hME, det_smul, conjugatedMatrix_det, Fintype.card_fin] at h1
    exact (mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hc0)) hdet) h1
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hMdet, Units.mk0 c hc0, ?_⟩
  rw [GeneralLinearGroup.val_mkOfDetNeZero, hME, conjCoord_eq, Units.val_mk0, smul_smul,
    mul_inv_cancel₀ hc0, one_smul]

@[expose] noncomputable def thetaHom {t : Eˣ} (ht : σ (t : E) = -(t : E))
    {B : (Fin 2 → E) ≃ₗ[E] V} (hB : ∀ x y, h (B x) (B y) = hyperbolicForm σ x y)
    (h90 : ∀ u : E, σ u * u = 1 → ∃ c : E, c ≠ 0 ∧ σ c * u = c) :
    isometryGroup h →* PGL(2, fixedSubfield E σ) where
  toFun g := ProjGenLinGroup.mk
    (Classical.choose (exists_isRep ht (coordMat_isometry hB g.2) h90))
  map_one' :=
    ((Classical.choose_spec (exists_isRep ht (coordMat_isometry hB
      (1 : isometryGroup h).2) h90)).mk_eq (isRep_one B t)).trans ProjGenLinGroup.mk_one
  map_mul' g₁ g₂ := by
    rw [← map_mul]
    exact (Classical.choose_spec (exists_isRep ht (coordMat_isometry hB (g₁ * g₂).2) h90)).mk_eq
      ((Classical.choose_spec (exists_isRep ht (coordMat_isometry hB g₁.2) h90)).mul
        (Classical.choose_spec (exists_isRep ht (coordMat_isometry hB g₂.2) h90)))

theorem thetaHom_apply_of_isRep {t : Eˣ} (ht : σ (t : E) = -(t : E))
    {B : (Fin 2 → E) ≃ₗ[E] V} (hB : ∀ x y, h (B x) (B y) = hyperbolicForm σ x y)
    (h90 : ∀ u : E, σ u * u = 1 → ∃ c : E, c ≠ 0 ∧ σ c * u = c) {g : isometryGroup h}
    {A₀ : GL (Fin 2) (fixedSubfield E σ)} (hrep : IsRep σ B t g A₀) :
    thetaHom ht hB h90 g = ProjGenLinGroup.mk A₀ :=
  (Classical.choose_spec (exists_isRep ht (coordMat_isometry hB g.2) h90)).mk_eq hrep

theorem coordMat_eq_smul {B : (Fin 2 → E) ≃ₗ[E] V} {g : V ≃ₗ[E] V} {c : E}
    (hc : ∀ v, g v = c • v) : coordMat B g = c • 1 := by
  have e : ((B.trans g).trans B.symm).toLinearMap = c • LinearMap.id :=
    LinearMap.ext fun y => by simp [hc]
  rw [coordMat, e, map_smul, LinearMap.toMatrix'_id]

end CFSG.LieType.SteinbergBR

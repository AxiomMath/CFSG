module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi

public noncomputable section

namespace CFSG.LinearAlgebra

open Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCLinComm

variable {n : ℕ} {K : Type} [Field K]

theorem glFieldAut_eq_glAut (n : ℕ) (K : Type) [Field K] :
    glFieldAut (Fin n) K = glAut (ι := Fin n) (K := K) := by
  ext σ A i j
  rfl

@[expose] def coordinateSemilinearEquivSemiGL (n : ℕ) (K : Type) [Field K] :
    coordinateSemilinearGroup n K ≃* SemiGL (Fin n) K where
  toFun g := ⟨g.left, g.right⟩
  invFun g := ⟨g.left, g.right⟩
  left_inv g := by
    apply SemidirectProduct.ext <;> rfl
  right_inv g := by
    apply SemidirectProduct.ext <;> rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change g.left * glFieldAut (Fin n) K g.right h.left =
        g.left * glAut (ι := Fin n) (K := K) g.right h.left
      have happ : glFieldAut (Fin n) K g.right h.left = glAut g.right h.left :=
        congrArg (fun f : (K ≃+* K) →* MulAut (GL (Fin n) K) => f g.right h.left)
          (glFieldAut_eq_glAut n K)
      rw [happ]
    · rfl

@[simp]
theorem coordinateSemilinearEquivSemiGL_apply_left (n : ℕ) (K : Type) [Field K]
    (g : coordinateSemilinearGroup n K) :
    (coordinateSemilinearEquivSemiGL n K g).left = g.left := rfl

@[simp]
theorem coordinateSemilinearEquivSemiGL_apply_right (n : ℕ) (K : Type) [Field K]
    (g : coordinateSemilinearGroup n K) :
    (coordinateSemilinearEquivSemiGL n K g).right = g.right := rfl

@[simp]
theorem coordinateSemilinearEquivSemiGL_symm_apply_left (n : ℕ) (K : Type) [Field K]
    (g : SemiGL (Fin n) K) :
    ((coordinateSemilinearEquivSemiGL n K).symm g).left = g.left := rfl

@[simp]
theorem coordinateSemilinearEquivSemiGL_symm_apply_right (n : ℕ) (K : Type) [Field K]
    (g : SemiGL (Fin n) K) :
    ((coordinateSemilinearEquivSemiGL n K).symm g).right = g.right := rfl

@[expose] def coordinateSemilinearAct (n : ℕ) (K : Type) [Field K] :
    coordinateSemilinearGroup n K →* RingAut (Matrix (Fin n) (Fin n) K) :=
  (semilinAct n K).comp (coordinateSemilinearEquivSemiGL n K).toMonoidHom

@[expose] def coordinateSemilinearGLAct (n : ℕ) (K : Type) [Field K] :
    coordinateSemilinearGroup n K →* MulAut (GL (Fin n) K) :=
  (semilinGLAct n K).comp (coordinateSemilinearEquivSemiGL n K).toMonoidHom

theorem coordinateSemilinearAct_mk (n : ℕ) (K : Type) [Field K]
    (A : GL (Fin n) K) (σ : K ≃+* K) (Y : Matrix (Fin n) (Fin n) K) :
    coordinateSemilinearAct n K (⟨A, σ⟩ : coordinateSemilinearGroup n K) Y =
      (A : Matrix (Fin n) (Fin n) K) * Y.map σ *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  change semilinAct n K (⟨A, σ⟩ : SemiGL (Fin n) K) Y = _
  rw [semilinAct_mk]

theorem coordinateSemilinearGLAct_mk (n : ℕ) (K : Type) [Field K]
    (A : GL (Fin n) K) (σ : K ≃+* K) (X : GL (Fin n) K) :
    coordinateSemilinearGLAct n K (⟨A, σ⟩ : coordinateSemilinearGroup n K) X =
      A * glAut σ X * A⁻¹ := by
  change semilinGLAct n K (⟨A, σ⟩ : SemiGL (Fin n) K) X = _
  rw [semilinGLAct_mk]

theorem coe_coordinateSemilinearGLAct (n : ℕ) (K : Type) [Field K]
    (g : coordinateSemilinearGroup n K) (X : GL (Fin n) K) :
    ((coordinateSemilinearGLAct n K g X : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      coordinateSemilinearAct n K g (X : Matrix (Fin n) (Fin n) K) := by
  change ((semilinGLAct n K (coordinateSemilinearEquivSemiGL n K g) X : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
    semilinAct n K (coordinateSemilinearEquivSemiGL n K g)
      (X : Matrix (Fin n) (Fin n) K)
  exact coe_semilinGLAct (coordinateSemilinearEquivSemiGL n K g) X

@[simp]
theorem coordinateSemilinearAct_mul_apply (n : ℕ) (K : Type) [Field K]
    (g h : coordinateSemilinearGroup n K) (Y : Matrix (Fin n) (Fin n) K) :
    coordinateSemilinearAct n K (g * h) Y =
      coordinateSemilinearAct n K g (coordinateSemilinearAct n K h Y) := by
  rw [map_mul]
  rfl

@[simp]
theorem coordinateSemilinearGLAct_mul_apply (n : ℕ) (K : Type) [Field K]
    (g h : coordinateSemilinearGroup n K) (X : GL (Fin n) K) :
    coordinateSemilinearGLAct n K (g * h) X =
      coordinateSemilinearGLAct n K g (coordinateSemilinearGLAct n K h X) := by
  rw [map_mul]
  rfl

theorem coordinateSemilinearGLAct_scalar (n : ℕ) (K : Type) [Field K]
    (g : coordinateSemilinearGroup n K) (c : Kˣ) :
    coordinateSemilinearGLAct n K g (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) (Units.map g.right.toMonoidHom c) := by
  have h : glAut g.right (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) (Units.map g.right.toMonoidHom c) := by
    apply Units.ext
    rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero g.right)]
    rfl
  have hg : g = (⟨g.left, g.right⟩ : coordinateSemilinearGroup n K) := rfl
  rw [hg, coordinateSemilinearGLAct_mk]
  change g.left * glAut g.right (GeneralLinearGroup.scalar (Fin n) c) * g.left⁻¹ = _
  rw [h, (commute_scalar_gl (Units.map g.right.toMonoidHom c) g.left).symm.eq,
    mul_assoc, mul_inv_cancel, mul_one]

theorem coordinateSemilinearAct_inl (n : ℕ) (K : Type) [Field K]
    (A : GL (Fin n) K) (Y : Matrix (Fin n) (Fin n) K) :
    coordinateSemilinearAct n K (SemidirectProduct.inl A) Y = conjRingAut n K A Y := by
  rw [show (SemidirectProduct.inl A : coordinateSemilinearGroup n K) =
      (⟨A, 1⟩ : coordinateSemilinearGroup n K) from rfl,
    coordinateSemilinearAct_mk, conjRingAut_apply]
  simp

theorem coordinateSemilinearGLAct_inl (n : ℕ) (K : Type) [Field K]
    (A X : GL (Fin n) K) :
    coordinateSemilinearGLAct n K (SemidirectProduct.inl A) X = A * X * A⁻¹ := by
  rw [show (SemidirectProduct.inl A : coordinateSemilinearGroup n K) =
      (⟨A, 1⟩ : coordinateSemilinearGroup n K) from rfl,
    coordinateSemilinearGLAct_mk]
  simp

theorem coordinateSemilinear_inl_conj (n : ℕ) (K : Type) [Field K]
    (g : coordinateSemilinearGroup n K) (X : GL (Fin n) K) :
    g * SemidirectProduct.inl X * g⁻¹ =
      SemidirectProduct.inl (coordinateSemilinearGLAct n K g X) := by
  obtain ⟨B, σ⟩ := g
  rw [coordinateSemilinearGLAct_mk]
  have happ : glFieldAut (Fin n) K σ X = glAut σ X :=
    congrArg (fun f : (K ≃+* K) →* MulAut (GL (Fin n) K) => f σ X)
      (glFieldAut_eq_glAut n K)
  have hfield : glFieldAut (Fin n) K σ (glFieldAut (Fin n) K σ⁻¹ B⁻¹) = B⁻¹ := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      mul_one]
    rw [hfield, happ]
  · simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right]

theorem tau_conj_eq_coordinateSemilinearGLAct
    {A : Type*} [Group A] (n : ℕ) (K : Type) [Field K]
    (rho : A →* coordinateSemilinearGroup n K)
    (tau : (SemidirectProduct.rightHom.comp rho).ker →* GL (Fin n) K)
    (htau : ∀ j : (SemidirectProduct.rightHom.comp rho).ker,
      rho (j : A) = SemidirectProduct.inl (tau j))
    (a : A) (j j' : (SemidirectProduct.rightHom.comp rho).ker)
    (hconj : (j' : A) = a * (j : A) * a⁻¹) :
    tau j' = coordinateSemilinearGLAct n K (rho a) (tau j) := by
  apply SemidirectProduct.inl_injective (N := GL (Fin n) K) (G := K ≃+* K)
    (φ := glFieldAut (Fin n) K)
  rw [← htau j']
  calc
    rho (j' : A) = rho (a * (j : A) * a⁻¹) := by rw [hconj]
    _ = rho a * rho (j : A) * (rho a)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = rho a * SemidirectProduct.inl (tau j) * (rho a)⁻¹ := by rw [htau j]
    _ = SemidirectProduct.inl (coordinateSemilinearGLAct n K (rho a) (tau j)) :=
      coordinateSemilinear_inl_conj n K (rho a) (tau j)

theorem tau_range_map_coordinateSemilinearGLAct_eq
    {A : Type*} [Group A] (n : ℕ) (K : Type) [Field K]
    (rho : A →* coordinateSemilinearGroup n K)
    (tau : (SemidirectProduct.rightHom.comp rho).ker →* GL (Fin n) K)
    (htau : ∀ j : (SemidirectProduct.rightHom.comp rho).ker,
      rho (j : A) = SemidirectProduct.inl (tau j))
    (a : A) :
    (tau.range).map (coordinateSemilinearGLAct n K (rho a)).toMonoidHom = tau.range := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    rcases hy with ⟨j, hj⟩
    rw [← hj]
    have hj1 : (SemidirectProduct.rightHom.comp rho) (j : A) = 1 := j.property
    let j' : (SemidirectProduct.rightHom.comp rho).ker :=
      ⟨a * (j : A) * a⁻¹, by
        change (SemidirectProduct.rightHom.comp rho) (a * (j : A) * a⁻¹) = 1
        simp only [MonoidHom.comp_apply, map_mul, map_inv, hj1, mul_one, mul_inv_cancel]⟩
    exact ⟨j', tau_conj_eq_coordinateSemilinearGLAct n K rho tau htau a j j' rfl⟩
  · rintro x ⟨j, rfl⟩
    have hj1 : (SemidirectProduct.rightHom.comp rho) (j : A) = 1 := j.property
    let j₀ : (SemidirectProduct.rightHom.comp rho).ker :=
      ⟨a⁻¹ * (j : A) * a, by
        change (SemidirectProduct.rightHom.comp rho) (a⁻¹ * (j : A) * a) = 1
        simp only [MonoidHom.comp_apply, map_mul, map_inv, hj1, mul_one, inv_mul_cancel]⟩
    have hconj : (j : A) = a * (j₀ : A) * a⁻¹ := by
      change (j : A) = a * (a⁻¹ * (j : A) * a) * a⁻¹
      group
    refine ⟨tau j₀, ⟨j₀, rfl⟩, ?_⟩
    exact (tau_conj_eq_coordinateSemilinearGLAct n K rho tau htau a j₀ j hconj).symm

end CFSG.LinearAlgebra

module

public import CFSG.LieType.AlgebraicGroups.GLCoordDomain
public import CFSG.Blueprint.ChevalleyRoots
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct WithConv CFSG.Blueprint.Chevalley

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def glPoint (g : Matrix.GeneralLinearGroup ι k) : GLCoord k ι →ₐ[k] k :=
  GLCoord.lift k ι (g : Matrix ι ι k) ((g : Matrix ι ι k).det)⁻¹ (mul_inv_cancel₀ g.det_ne_zero)

@[simp] theorem glPoint_glEntry (g : Matrix.GeneralLinearGroup ι k) (i j : ι) :
    glPoint g (glEntry k ι i j) = (g : Matrix ι ι k) i j :=
  GLCoord.lift_glEntry k ι _ _ (mul_inv_cancel₀ g.det_ne_zero) i j

@[simp] theorem glPoint_glDetInv (g : Matrix.GeneralLinearGroup ι k) :
    glPoint g (glDetInv k ι) = ((g : Matrix ι ι k).det)⁻¹ :=
  GLCoord.lift_glDetInv k ι _ _ (mul_inv_cancel₀ g.det_ne_zero)

@[expose] def pointMatrix (φ : GLCoord k ι →ₐ[k] k) : Matrix ι ι k :=
  Matrix.of fun i j => φ (glEntry k ι i j)

theorem det_pointMatrix_mul (φ : GLCoord k ι →ₐ[k] k) :
    (pointMatrix φ).det * φ (glDetInv k ι) = 1 := by
  rw [pointMatrix, ← GLCoord.map_det, ← map_mul, det_glEntryMatrix_mul_glDetInv, map_one]

@[expose] def pointGL (φ : GLCoord k ι →ₐ[k] k) : Matrix.GeneralLinearGroup ι k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (pointMatrix φ)
    (left_ne_zero_of_mul_eq_one (det_pointMatrix_mul φ))

theorem convMul_glEntry (φ ψ : WithConv (GLCoord k ι →ₐ[k] k)) (i j : ι) :
    (φ * ψ).ofConv (glEntry k ι i j) =
      ∑ l, φ.ofConv (glEntry k ι i l) * ψ.ofConv (glEntry k ι l j) := by
  rw [AlgHom.convMul_apply, comul_glEntry, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul]

theorem convMul_glDetInv (φ ψ : WithConv (GLCoord k ι →ₐ[k] k)) :
    (φ * ψ).ofConv (glDetInv k ι) = φ.ofConv (glDetInv k ι) * ψ.ofConv (glDetInv k ι) := by
  rw [AlgHom.convMul_apply, comul_glDetInv, Algebra.TensorProduct.lift_tmul]

@[expose] def glPointEquiv :
    Matrix.GeneralLinearGroup ι k ≃* WithConv (GLCoord k ι →ₐ[k] k) where
  toFun g := toConv (glPoint g)
  invFun φ := pointGL φ.ofConv
  left_inv g := Matrix.GeneralLinearGroup.ext fun i j => by
    simp [pointGL, pointMatrix]
  right_inv φ := by
    refine WithConv.ext (GLCoord.algHom_ext k ι (fun i j => ?_) ?_)
    · simp [pointGL, pointMatrix]
    · simp only [glPoint_glDetInv, pointGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact inv_eq_of_mul_eq_one_right (det_pointMatrix_mul φ.ofConv)
  map_mul' g h := by
    refine WithConv.ext (GLCoord.algHom_ext k ι (fun i j => ?_) ?_)
    · simp [convMul_glEntry, Matrix.mul_apply]
    · simp only [convMul_glDetInv, glPoint_glDetInv, Units.val_mul, Matrix.det_mul, mul_inv]

@[simp] theorem glPointEquiv_apply_glEntry (g : Matrix.GeneralLinearGroup ι k) (i j : ι) :
    (glPointEquiv g).ofConv (glEntry k ι i j) = (g : Matrix ι ι k) i j :=
  glPoint_glEntry g i j

@[simp] theorem glPointEquiv_apply_glDetInv (g : Matrix.GeneralLinearGroup ι k) :
    (glPointEquiv g).ofConv (glDetInv k ι) = ((g : Matrix ι ι k).det)⁻¹ :=
  glPoint_glDetInv g

@[simp] theorem glPointEquiv_symm_apply (φ : WithConv (GLCoord k ι →ₐ[k] k)) (i j : ι) :
    ((glPointEquiv.symm φ : Matrix.GeneralLinearGroup ι k) : Matrix ι ι k) i j =
      φ.ofConv (glEntry k ι i j) :=
  rfl

@[expose] def modGLEquivGL (τ : Tag) (K : Type*) [Field K] :
    ModGL τ K ≃* Matrix.GeneralLinearGroup (Label τ) K :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv
    (Finsupp.basisSingleOne : Module.Basis (Label τ) K (Label τ →₀ K))).toRingEquiv.toMulEquiv

@[simp] theorem modGLEquivGL_apply (τ : Tag) (K : Type*) [Field K]
    (g : ModGL τ K) (a b : Label τ) :
    (modGLEquivGL τ K g : Matrix (Label τ) (Label τ) K) a b =
      ((g : Module.End K (RootModule τ K)) (Finsupp.single b 1)) a := by
  simp [modGLEquivGL, LinearMap.toMatrixAlgEquiv_apply]

theorem GLCoord_structure (k : Type*) [Field k] (ι : Type*)
    [Fintype ι] [DecidableEq ι] :
    glIdeal k ι = Ideal.span {glDet k ι * glT k ι - 1} ∧
    ((glIdeal k ι).restrictScalars k).IsCoideal ∧
    Algebra.FiniteType k (GLCoord k ι) ∧ IsDomain (GLCoord k ι) ∧
    Algebra.adjoin k (Set.range (fun p : ι × ι => glEntry k ι p.1 p.2) ∪ {glDetInv k ι}) = ⊤ ∧
    (glEntryMatrix k ι).det * glDetInv k ι = 1 ∧
    (∀ i j, Coalgebra.comul (R := k) (glEntry k ι i j) =
      ∑ l, glEntry k ι i l ⊗ₜ glEntry k ι l j) ∧
    Coalgebra.comul (R := k) (glDetInv k ι) = glDetInv k ι ⊗ₜ glDetInv k ι ∧
    (∀ i j, Coalgebra.counit (R := k) (glEntry k ι i j) = if i = j then 1 else 0) ∧
    Coalgebra.counit (R := k) (glDetInv k ι) = 1 ∧
    (∀ i j, HopfAlgebra.antipode k (glEntry k ι i j) =
      glDetInv k ι * (glEntryMatrix k ι).adjugate i j) ∧
    HopfAlgebra.antipode k (glDetInv k ι) = (glEntryMatrix k ι).det ∧
    (∀ g h : Matrix.GeneralLinearGroup ι k,
      glPointEquiv (g * h) = glPointEquiv g * glPointEquiv h) ∧
    (∀ (g : Matrix.GeneralLinearGroup ι k) (i j : ι),
      (glPointEquiv g).ofConv (glEntry k ι i j) = (g : Matrix ι ι k) i j) ∧
    (∀ g : Matrix.GeneralLinearGroup ι k,
      (glPointEquiv g).ofConv (glDetInv k ι) = ((g : Matrix ι ι k).det)⁻¹) ∧
    ∀ (τ : Tag) (g : ModGL τ k) (a b : Label τ),
      (modGLEquivGL τ k g : Matrix (Label τ) (Label τ) k) a b =
        ((g : Module.End k (RootModule τ k)) (Finsupp.single b 1)) a :=
  ⟨rfl, inferInstance, inferInstance, inferInstance, GLCoord.adjoin_eq_top k ι,
    det_glEntryMatrix_mul_glDetInv k ι, comul_glEntry k ι, comul_glDetInv k ι,
    counit_glEntry k ι, counit_glDetInv k ι, antipode_glEntry k ι, antipode_glDetInv k ι,
    map_mul glPointEquiv, glPointEquiv_apply_glEntry, glPointEquiv_apply_glDetInv,
    fun τ g a b => modGLEquivGL_apply τ k g a b⟩

end CFSG.LieType.AlgebraicGroups

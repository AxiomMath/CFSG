module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Algebra.Group.Subgroup.Basic

public noncomputable section

namespace CFSG.LieType.Steinberg.Twist

variable {k : Type*} [Field k] {d : ℕ}

@[expose] def toMat (A : Module.End k (Fin d →₀ k)) : Matrix (Fin d) (Fin d) k :=
  LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne A

@[expose] def ofMat (M : Matrix (Fin d) (Fin d) k) : Module.End k (Fin d →₀ k) :=
  Matrix.toLin Finsupp.basisSingleOne Finsupp.basisSingleOne M

theorem ofMat_toMat (A : Module.End k (Fin d →₀ k)) : ofMat (toMat A) = A :=
  Matrix.toLin_toMatrix _ _ A

theorem toMat_ofMat (M : Matrix (Fin d) (Fin d) k) : toMat (ofMat M) = M :=
  LinearMap.toMatrix_toLin _ _ M

theorem toMat_mul (A B : Module.End k (Fin d →₀ k)) : toMat (A * B) = toMat A * toMat B :=
  LinearMap.toMatrix_mul _ A B

theorem toMat_one : toMat (1 : Module.End k (Fin d →₀ k)) = 1 := LinearMap.toMatrix_one _

theorem ofMat_mul (M N : Matrix (Fin d) (Fin d) k) : ofMat (M * N) = ofMat M * ofMat N :=
  Matrix.toLin_mul _ _ _ M N

@[expose] def frobT (θ : k →+* k) (A : Module.End k (Fin d →₀ k)) : Module.End k (Fin d →₀ k) :=
  ofMat ((toMat A).transpose.map θ)

theorem frobT_mul (θ : k →+* k) (A B : Module.End k (Fin d →₀ k)) :
    frobT θ (A * B) = frobT θ B * frobT θ A := by
  simp only [frobT, toMat_mul, Matrix.transpose_mul, Matrix.map_mul, ofMat_mul]

theorem frobT_one (θ : k →+* k) : frobT θ (1 : Module.End k (Fin d →₀ k)) = 1 := by
  rw [frobT, toMat_one, Matrix.transpose_one, Matrix.map_one _ (map_zero θ) (map_one θ),
    ← toMat_one, ofMat_toMat]

theorem frobT_add (θ : k →+* k) (A B : Module.End k (Fin d →₀ k)) :
    frobT θ (A + B) = frobT θ A + frobT θ B := by
  have h : toMat (A + B) = toMat A + toMat B := map_add _ A B
  rw [frobT, h, Matrix.transpose_add, Matrix.map_add _ (map_add θ), ofMat, map_add]
  rfl

theorem frobT_smul (θ : k →+* k) (c : k) (A : Module.End k (Fin d →₀ k)) :
    frobT θ (c • A) = θ c • frobT θ A := by
  have h : toMat (c • A) = c • toMat A := map_smul _ c A
  have h' : ((c • toMat A).transpose.map θ) = θ c • (toMat A).transpose.map θ := by
    ext i j
    simp [map_mul]
  rw [frobT, h, h', ofMat, map_smul]
  rfl

theorem frobT_sub (θ : k →+* k) (A B : Module.End k (Fin d →₀ k)) :
    frobT θ (A - B) = frobT θ A - frobT θ B := by
  have h : toMat (A - B) = toMat A - toMat B := map_sub _ A B
  rw [frobT, h, Matrix.transpose_sub, Matrix.map_sub _ (map_sub θ), ofMat, map_sub]
  rfl

@[expose] def dualHom (θ : k →+* k) :
    (Module.End k (Fin d →₀ k))ˣ →* (Module.End k (Fin d →₀ k))ˣ where
  toFun g :=
    { val := frobT θ (g⁻¹ : (Module.End k (Fin d →₀ k))ˣ)
      inv := frobT θ g
      val_inv := by rw [← frobT_mul, Units.mul_inv, frobT_one]
      inv_val := by rw [← frobT_mul, Units.inv_mul, frobT_one] }
  map_one' := by ext1; simp [frobT_one]
  map_mul' g h := by ext1; simp [mul_inv_rev, frobT_mul]

@[expose] def twistHom (θ : k →+* k) (P : (Module.End k (Fin d →₀ k))ˣ) :
    (Module.End k (Fin d →₀ k))ˣ →* (Module.End k (Fin d →₀ k))ˣ :=
  (MulAut.conj P).toMonoidHom.comp (dualHom θ)

theorem twistHom_apply (θ : k →+* k) (P g : (Module.End k (Fin d →₀ k))ˣ) :
    twistHom θ P g = P * dualHom θ g * P⁻¹ := rfl

@[expose] def fixedPoints (θ : k →+* k) (P : (Module.End k (Fin d →₀ k))ˣ) :
    Subgroup (Module.End k (Fin d →₀ k))ˣ :=
  MonoidHom.eqLocus (twistHom θ P) (MonoidHom.id _)

end CFSG.LieType.Steinberg.Twist

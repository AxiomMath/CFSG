module

public import Mathlib.RingTheory.Bialgebra.Quotient
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct MvPolynomial

variable (k : Type*) [Field k] (ι : Type*)

@[expose] def GLPoly : Type _ := MvPolynomial (ι × ι ⊕ Unit) k

instance : CommRing (GLPoly k ι) := inferInstanceAs (CommRing (MvPolynomial (ι × ι ⊕ Unit) k))

instance : Algebra k (GLPoly k ι) := inferInstanceAs (Algebra k (MvPolynomial (ι × ι ⊕ Unit) k))

@[expose] def glX (i j : ι) : GLPoly k ι := X (Sum.inl (i, j))

@[expose] def glT : GLPoly k ι := X (Sum.inr ())

@[expose] def glMatrix : Matrix ι ι (GLPoly k ι) := Matrix.of (glX k ι)

@[simp] theorem glMatrix_apply (i j : ι) : glMatrix k ι i j = glX k ι i j := rfl

theorem GLPoly.algHom_ext {A : Type*} [Semiring A] [Algebra k A] {f g : GLPoly k ι →ₐ[k] A}
    (hx : ∀ i j, f (glX k ι i j) = g (glX k ι i j)) (ht : f (glT k ι) = g (glT k ι)) :
    f = g :=
  MvPolynomial.algHom_ext fun v => by
    rcases v with ⟨i, j⟩ | ⟨⟩
    · exact hx i j
    · exact ht

@[expose] def GLPoly.lift {A : Type*} [CommSemiring A] [Algebra k A] (x : Matrix ι ι A) (t : A) :
    GLPoly k ι →ₐ[k] A :=
  aeval (Sum.elim (fun p => x p.1 p.2) fun _ => t)

@[simp] theorem GLPoly.lift_glX {A : Type*} [CommSemiring A] [Algebra k A] (x : Matrix ι ι A)
    (t : A) (i j : ι) : GLPoly.lift k ι x t (glX k ι i j) = x i j :=
  aeval_X _ _

@[simp] theorem GLPoly.lift_glT {A : Type*} [CommSemiring A] [Algebra k A] (x : Matrix ι ι A)
    (t : A) : GLPoly.lift k ι x t (glT k ι) = t :=
  aeval_X _ _

section Comul

variable [Fintype ι]

@[expose] def glComul : GLPoly k ι →ₐ[k] GLPoly k ι ⊗[k] GLPoly k ι :=
  GLPoly.lift k ι (Matrix.of fun i j => ∑ l, glX k ι i l ⊗ₜ glX k ι l j) (glT k ι ⊗ₜ glT k ι)

@[simp] theorem glComul_glX (i j : ι) :
    glComul k ι (glX k ι i j) = ∑ l, glX k ι i l ⊗ₜ glX k ι l j :=
  GLPoly.lift_glX _ _ _ _ _ _

@[simp] theorem glComul_glT : glComul k ι (glT k ι) = glT k ι ⊗ₜ glT k ι :=
  GLPoly.lift_glT _ _ _ _

theorem glComul_coassoc :
    (Algebra.TensorProduct.assoc k k k (GLPoly k ι) (GLPoly k ι) (GLPoly k ι)).toAlgHom.comp
        ((Algebra.TensorProduct.map (glComul k ι) (.id k (GLPoly k ι))).comp (glComul k ι)) =
      (Algebra.TensorProduct.map (.id k (GLPoly k ι)) (glComul k ι)).comp (glComul k ι) := by
  refine GLPoly.algHom_ext k ι (fun i j => ?_) ?_
  · simp only [AlgHom.comp_apply, glComul_glX, map_sum, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, sum_tmul, tmul_sum, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.assoc_tmul]
    exact Finset.sum_comm
  · simp only [AlgHom.comp_apply, glComul_glT, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.assoc_tmul]

end Comul

section Counit

variable [DecidableEq ι]

@[expose] def glCounit : GLPoly k ι →ₐ[k] k :=
  GLPoly.lift k ι (Matrix.of fun i j => if i = j then 1 else 0) 1

@[simp] theorem glCounit_glX (i j : ι) : glCounit k ι (glX k ι i j) = if i = j then 1 else 0 :=
  GLPoly.lift_glX _ _ _ _ _ _

@[simp] theorem glCounit_glT : glCounit k ι (glT k ι) = 1 :=
  GLPoly.lift_glT _ _ _ _

end Counit

variable [Fintype ι] [DecidableEq ι]

@[expose] def glDet : GLPoly k ι := (glMatrix k ι).det

theorem GLPoly.map_glDet {A : Type*} [CommRing A] [Algebra k A] (f : GLPoly k ι →ₐ[k] A) :
    f (glDet k ι) = (Matrix.of fun i j => f (glX k ι i j)).det := by
  rw [glDet, AlgHom.map_det]
  rfl

theorem glCounit_rTensor :
    (Algebra.TensorProduct.map (glCounit k ι) (.id k (GLPoly k ι))).comp (glComul k ι) =
      (Algebra.TensorProduct.lid k (GLPoly k ι)).symm := by
  refine GLPoly.algHom_ext k ι (fun i j => ?_) ?_
  · simp only [AlgHom.comp_apply, glComul_glX, map_sum, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, glCounit_glX, ite_tmul, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.lid_symm_apply]
    rw [Finset.sum_ite_eq]
    simp
  · simp only [AlgHom.comp_apply, glComul_glT, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      glCounit_glT, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.lid_symm_apply]

theorem glCounit_lTensor :
    (Algebra.TensorProduct.map (.id k (GLPoly k ι)) (glCounit k ι)).comp (glComul k ι) =
      (Algebra.TensorProduct.rid k k (GLPoly k ι)).symm := by
  refine GLPoly.algHom_ext k ι (fun i j => ?_) ?_
  · simp only [AlgHom.comp_apply, glComul_glX, map_sum, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, glCounit_glX, tmul_ite, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.rid_symm_apply]
    rw [Finset.sum_ite_eq']
    simp
  · simp only [AlgHom.comp_apply, glComul_glT, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      glCounit_glT, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.rid_symm_apply]

instance : Bialgebra k (GLPoly k ι) :=
  Bialgebra.ofAlgHom (glComul k ι) (glCounit k ι) (glComul_coassoc k ι) (glCounit_rTensor k ι)
    (glCounit_lTensor k ι)

theorem GLPoly.comulAlgHom_eq : Bialgebra.comulAlgHom k (GLPoly k ι) = glComul k ι :=
  AlgHom.ext fun _ => rfl

theorem GLPoly.counitAlgHom_eq : Bialgebra.counitAlgHom k (GLPoly k ι) = glCounit k ι :=
  AlgHom.ext fun _ => rfl

theorem glComul_glDet : glComul k ι (glDet k ι) = glDet k ι ⊗ₜ glDet k ι := by
  have h : (Matrix.of fun i j => glComul k ι (glX k ι i j)) =
      (glMatrix k ι).map
          (Algebra.TensorProduct.includeLeft : GLPoly k ι →ₐ[k] GLPoly k ι ⊗[k] GLPoly k ι) *
        (glMatrix k ι).map
          (Algebra.TensorProduct.includeRight : GLPoly k ι →ₐ[k] GLPoly k ι ⊗[k] GLPoly k ι) := by
    ext i j
    simp [Matrix.mul_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [GLPoly.map_glDet, h, Matrix.det_mul]
  have hL := AlgHom.map_det (Algebra.TensorProduct.includeLeft (R := k) (S := k)
    (A := GLPoly k ι) (B := GLPoly k ι)) (glMatrix k ι)
  have hR := AlgHom.map_det (Algebra.TensorProduct.includeRight (R := k)
    (A := GLPoly k ι) (B := GLPoly k ι)) (glMatrix k ι)
  rw [AlgHom.mapMatrix_apply] at hL hR
  rw [← hL, ← hR, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul]
  rfl

theorem glCounit_glDet : glCounit k ι (glDet k ι) = 1 := by
  rw [GLPoly.map_glDet]
  have h : (Matrix.of fun i j => glCounit k ι (glX k ι i j)) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  rw [h, Matrix.det_one]

@[expose] def glIdeal : Ideal (GLPoly k ι) := Ideal.span {glDet k ι * glT k ι - 1}

theorem mem_glIdeal {a : GLPoly k ι} :
    a ∈ glIdeal k ι ↔ ∃ b, b * (glDet k ι * glT k ι - 1) = a :=
  Ideal.mem_span_singleton'

instance : ((glIdeal k ι).restrictScalars k).IsCoideal where
  counit_eq_zero x hx := by
    obtain ⟨b, rfl⟩ := (mem_glIdeal k ι).1 hx
    change glCounit k ι (b * (glDet k ι * glT k ι - 1)) = 0
    rw [map_mul, map_sub, map_mul, glCounit_glDet, glCounit_glT, map_one, mul_one, sub_self,
      mul_zero]
  map_mkQ_comul_eq_zero x hx := by
    obtain ⟨b, rfl⟩ := (mem_glIdeal k ι).1 hx
    change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (glIdeal k ι))
      (Ideal.Quotient.mkₐ k (glIdeal k ι)) (glComul k ι (b * (glDet k ι * glT k ι - 1))) = 0
    have h1 : Ideal.Quotient.mkₐ k (glIdeal k ι) (glDet k ι * glT k ι) = 1 := by
      rw [← map_one (Ideal.Quotient.mkₐ k (glIdeal k ι)), Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact Ideal.subset_span rfl
    rw [map_mul, map_mul, map_sub, map_mul, glComul_glDet, glComul_glT, map_one,
      Algebra.TensorProduct.tmul_mul_tmul, map_sub, Algebra.TensorProduct.map_tmul, h1,
      map_one, Algebra.TensorProduct.one_def, sub_self, mul_zero]

end CFSG.LieType.AlgebraicGroups

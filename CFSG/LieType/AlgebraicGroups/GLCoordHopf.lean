module

public import CFSG.LieType.AlgebraicGroups.GLCoordBialgebra
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.FiniteType

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct

variable (k : Type*) [Field k] (ι : Type*) [Fintype ι] [DecidableEq ι]

abbrev GLCoord : Type _ := GLPoly k ι ⧸ glIdeal k ι

@[expose] def glEntry (i j : ι) : GLCoord k ι := Ideal.Quotient.mk (glIdeal k ι) (glX k ι i j)

@[expose] def glDetInv : GLCoord k ι := Ideal.Quotient.mk (glIdeal k ι) (glT k ι)

@[expose] def glEntryMatrix : Matrix ι ι (GLCoord k ι) := Matrix.of (glEntry k ι)

@[simp] theorem glEntryMatrix_apply (i j : ι) : glEntryMatrix k ι i j = glEntry k ι i j := rfl

@[simp] theorem mk_glX (i j : ι) :
    Ideal.Quotient.mk (glIdeal k ι) (glX k ι i j) = glEntry k ι i j :=
  rfl

@[simp] theorem mk_glT : Ideal.Quotient.mk (glIdeal k ι) (glT k ι) = glDetInv k ι :=
  rfl

theorem mk_glDet : Ideal.Quotient.mk (glIdeal k ι) (glDet k ι) = (glEntryMatrix k ι).det := by
  rw [glDet, RingHom.map_det]
  rfl

theorem det_glEntryMatrix_mul_glDetInv : (glEntryMatrix k ι).det * glDetInv k ι = 1 := by
  rw [← mk_glDet, ← mk_glT, ← map_mul, ← map_one (Ideal.Quotient.mk (glIdeal k ι)),
    Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span rfl

theorem glDetInv_mul_det_glEntryMatrix : glDetInv k ι * (glEntryMatrix k ι).det = 1 := by
  rw [mul_comm, det_glEntryMatrix_mul_glDetInv]

theorem GLCoord.algHom_ext {A : Type*} [Semiring A] [Algebra k A] {f g : GLCoord k ι →ₐ[k] A}
    (hx : ∀ i j, f (glEntry k ι i j) = g (glEntry k ι i j))
    (ht : f (glDetInv k ι) = g (glDetInv k ι)) : f = g :=
  Ideal.Quotient.algHom_ext k (GLPoly.algHom_ext k ι hx ht)

@[expose] def GLCoord.lift {A : Type*} [CommRing A] [Algebra k A] (x : Matrix ι ι A) (t : A)
    (h : x.det * t = 1) : GLCoord k ι →ₐ[k] A :=
  Ideal.Quotient.liftₐ (glIdeal k ι) (GLPoly.lift k ι x t) fun a ha => by
    obtain ⟨b, rfl⟩ := (mem_glIdeal k ι).1 ha
    have hx : (Matrix.of fun i j => GLPoly.lift k ι x t (glX k ι i j)) = x := by
      ext i j
      simp
    rw [map_mul, map_sub, map_mul, GLPoly.map_glDet, hx, GLPoly.lift_glT, map_one, h, sub_self,
      mul_zero]

@[simp] theorem GLCoord.lift_glEntry {A : Type*} [CommRing A] [Algebra k A] (x : Matrix ι ι A)
    (t : A) (h : x.det * t = 1) (i j : ι) : GLCoord.lift k ι x t h (glEntry k ι i j) = x i j :=
  GLPoly.lift_glX k ι x t i j

@[simp] theorem GLCoord.lift_glDetInv {A : Type*} [CommRing A] [Algebra k A] (x : Matrix ι ι A)
    (t : A) (h : x.det * t = 1) : GLCoord.lift k ι x t h (glDetInv k ι) = t :=
  GLPoly.lift_glT k ι x t

theorem GLCoord.map_det {A : Type*} [CommRing A] [Algebra k A] (f : GLCoord k ι →ₐ[k] A) :
    f (glEntryMatrix k ι).det = (Matrix.of fun i j => f (glEntry k ι i j)).det := by
  rw [AlgHom.map_det]
  rfl

@[simp] theorem comul_glEntry (i j : ι) :
    Coalgebra.comul (R := k) (glEntry k ι i j) = ∑ l, glEntry k ι i l ⊗ₜ glEntry k ι l j := by
  change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (glIdeal k ι))
    (Ideal.Quotient.mkₐ k (glIdeal k ι)) (glComul k ι (glX k ι i j)) = _
  rw [glComul_glX, map_sum]
  rfl

@[simp] theorem comul_glDetInv :
    Coalgebra.comul (R := k) (glDetInv k ι) = glDetInv k ι ⊗ₜ glDetInv k ι := by
  change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (glIdeal k ι))
    (Ideal.Quotient.mkₐ k (glIdeal k ι)) (glComul k ι (glT k ι)) = _
  rw [glComul_glT]
  rfl

@[simp] theorem counit_glEntry (i j : ι) :
    Coalgebra.counit (R := k) (glEntry k ι i j) = if i = j then 1 else 0 :=
  glCounit_glX k ι i j

@[simp] theorem counit_glDetInv : Coalgebra.counit (R := k) (glDetInv k ι) = 1 :=
  glCounit_glT k ι

theorem det_glDetInv_smul_adjugate_mul :
    (glDetInv k ι • (glEntryMatrix k ι).adjugate).det * (glEntryMatrix k ι).det = 1 := by
  rw [← Matrix.det_mul, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul,
    glDetInv_mul_det_glEntryMatrix, one_smul, Matrix.det_one]

@[expose] def glAntipode : GLCoord k ι →ₐ[k] GLCoord k ι :=
  GLCoord.lift k ι (glDetInv k ι • (glEntryMatrix k ι).adjugate) (glEntryMatrix k ι).det
    (det_glDetInv_smul_adjugate_mul k ι)

@[simp] theorem glAntipode_glEntry (i j : ι) :
    glAntipode k ι (glEntry k ι i j) = glDetInv k ι * (glEntryMatrix k ι).adjugate i j :=
  GLCoord.lift_glEntry k ι _ _ _ i j

@[simp] theorem glAntipode_glDetInv : glAntipode k ι (glDetInv k ι) = (glEntryMatrix k ι).det :=
  GLCoord.lift_glDetInv k ι _ _ _

theorem sum_glDetInv_mul_adjugate_mul (i j : ι) :
    ∑ l, glDetInv k ι * (glEntryMatrix k ι).adjugate i l * glEntry k ι l j =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.adjugate_mul (glEntryMatrix k ι)) i) j
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at h
  simp only [glEntryMatrix_apply] at h
  simp only [mul_assoc, ← Finset.mul_sum, h]
  split_ifs <;> simp [glDetInv_mul_det_glEntryMatrix]

theorem sum_mul_glDetInv_mul_adjugate (i j : ι) :
    ∑ l, glEntry k ι i l * (glDetInv k ι * (glEntryMatrix k ι).adjugate l j) =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mul_adjugate (glEntryMatrix k ι)) i) j
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at h
  simp only [glEntryMatrix_apply] at h
  simp only [mul_left_comm _ (glDetInv k ι), ← Finset.mul_sum, h]
  split_ifs <;> simp [glDetInv_mul_det_glEntryMatrix]

theorem glAntipode_rTensor :
    (Algebra.TensorProduct.lift (glAntipode k ι) (.id k (GLCoord k ι))
        fun _ _ ↦ Commute.all _ _).comp (Bialgebra.comulAlgHom k (GLCoord k ι)) =
      (Algebra.ofId k (GLCoord k ι)).comp (Bialgebra.counitAlgHom k (GLCoord k ι)) := by
  refine GLCoord.algHom_ext k ι (fun i j => ?_) ?_
  · simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.counitAlgHom_apply,
      comul_glEntry, counit_glEntry, map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
      glAntipode_glEntry, Algebra.ofId_apply, sum_glDetInv_mul_adjugate_mul]
    split_ifs <;> simp
  · simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.counitAlgHom_apply,
      comul_glDetInv, counit_glDetInv, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
      glAntipode_glDetInv, det_glEntryMatrix_mul_glDetInv, map_one]

theorem glAntipode_lTensor :
    (Algebra.TensorProduct.lift (.id k (GLCoord k ι)) (glAntipode k ι)
        fun _ _ ↦ Commute.all _ _).comp (Bialgebra.comulAlgHom k (GLCoord k ι)) =
      (Algebra.ofId k (GLCoord k ι)).comp (Bialgebra.counitAlgHom k (GLCoord k ι)) := by
  refine GLCoord.algHom_ext k ι (fun i j => ?_) ?_
  · simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.counitAlgHom_apply,
      comul_glEntry, counit_glEntry, map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
      glAntipode_glEntry, Algebra.ofId_apply, sum_mul_glDetInv_mul_adjugate]
    split_ifs <;> simp
  · simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.counitAlgHom_apply,
      comul_glDetInv, counit_glDetInv, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
      glAntipode_glDetInv, glDetInv_mul_det_glEntryMatrix, map_one]

instance : HopfAlgebra k (GLCoord k ι) :=
  HopfAlgebra.ofAlgHom (glAntipode k ι) (glAntipode_rTensor k ι) (glAntipode_lTensor k ι)

theorem GLCoord.antipodeAlgHom_eq : HopfAlgebra.antipodeAlgHom k (GLCoord k ι) = glAntipode k ι :=
  AlgHom.ext fun _ => rfl

@[simp] theorem antipode_glEntry (i j : ι) :
    HopfAlgebra.antipode k (glEntry k ι i j) = glDetInv k ι * (glEntryMatrix k ι).adjugate i j :=
  glAntipode_glEntry k ι i j

@[simp] theorem antipode_glDetInv :
    HopfAlgebra.antipode k (glDetInv k ι) = (glEntryMatrix k ι).det :=
  glAntipode_glDetInv k ι

theorem GLCoord.adjoin_eq_top :
    Algebra.adjoin k (Set.range (fun p : ι × ι => glEntry k ι p.1 p.2) ∪ {glDetInv k ι}) = ⊤ := by
  let π : MvPolynomial (ι × ι ⊕ Unit) k →ₐ[k] GLCoord k ι := Ideal.Quotient.mkₐ k (glIdeal k ι)
  have hle : Algebra.adjoin k (Set.range MvPolynomial.X) ≤
      (Algebra.adjoin k (Set.range (fun p : ι × ι => glEntry k ι p.1 p.2) ∪
        {glDetInv k ι})).comap π := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, rfl⟩
    rcases v with ⟨i, j⟩ | ⟨⟩
    · exact Algebra.subset_adjoin (Or.inl ⟨(i, j), rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr rfl)
  rw [MvPolynomial.adjoin_range_X] at hle
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact hle (Algebra.mem_top (R := k) (A := MvPolynomial (ι × ι ⊕ Unit) k) (x := p))

instance : Algebra.FiniteType k (GLPoly k ι) :=
  inferInstanceAs (Algebra.FiniteType k (MvPolynomial (ι × ι ⊕ Unit) k))

instance : Algebra.FiniteType k (GLCoord k ι) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k (glIdeal k ι))
    (Ideal.Quotient.mkₐ_surjective k (glIdeal k ι))

end CFSG.LieType.AlgebraicGroups

module

public import CFSG.LieType.AlgebraicGroups.ZariskiPoints
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.FiniteStability

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct WithConv

variable {k : Type} [Field k]

instance finiteType_tensorProduct {A B : Type} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B] :
    Algebra.FiniteType k (A ⊗[k] B) :=
  Algebra.FiniteType.trans (S := A) inferInstance inferInstance

variable {A B : Type} [CommRing A] [HopfAlgebra k A] [CommRing B] [HopfAlgebra k B]

variable (k A B) in
@[expose] def includeLeftBialgHom : A →ₐc[k] A ⊗[k] B :=
  (Bialgebra.TensorProduct.map (BialgHom.id k A) (Bialgebra.unitBialgHom k B)).comp
    (Bialgebra.TensorProduct.rid k k A).symm.toBialgHom

variable (k A B) in
@[expose] def includeRightBialgHom : B →ₐc[k] A ⊗[k] B :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom k A) (BialgHom.id k B)).comp
    (Bialgebra.TensorProduct.lid k B).symm.toBialgHom

theorem coe_includeLeftBialgHom :
    (includeLeftBialgHom k A B : A →ₐ[k] A ⊗[k] B) = Algebra.TensorProduct.includeLeft := by
  ext a
  simp [includeLeftBialgHom, Bialgebra.unitBialgHom]

theorem coe_includeRightBialgHom :
    (includeRightBialgHom k A B : B →ₐ[k] A ⊗[k] B) = Algebra.TensorProduct.includeRight := by
  ext b
  simp [includeRightBialgHom, Bialgebra.unitBialgHom]

theorem productMap_convMul (p q : WithConv (A →ₐ[k] k)) (p' q' : WithConv (B →ₐ[k] k)) :
    toConv (Algebra.TensorProduct.productMap p.ofConv p'.ofConv) *
        toConv (Algebra.TensorProduct.productMap q.ofConv q'.ofConv) =
      toConv (Algebra.TensorProduct.productMap (p * q).ofConv (p' * q').ofConv) := by
  set P := toConv (Algebra.TensorProduct.productMap p.ofConv p'.ofConv)
  set Q := toConv (Algebra.TensorProduct.productMap q.ofConv q'.ofConv)
  have hL : (P * Q).ofConv.comp Algebra.TensorProduct.includeLeft = (p * q).ofConv := by
    rw [← coe_includeLeftBialgHom, AlgHom.convMul_comp_bialgHom_distrib, coe_includeLeftBialgHom]
    simp only [P, Q, Algebra.TensorProduct.productMap_left, toConv_ofConv]
  have hR : (P * Q).ofConv.comp Algebra.TensorProduct.includeRight = (p' * q').ofConv := by
    rw [← coe_includeRightBialgHom, AlgHom.convMul_comp_bialgHom_distrib,
      coe_includeRightBialgHom]
    simp only [P, Q, Algebra.TensorProduct.productMap_right, toConv_ofConv]
  refine WithConv.ext (Algebra.TensorProduct.ext' fun a b => ?_)
  have ha := congrArg (fun φ : A →ₐ[k] k => φ a) hL
  have hb := congrArg (fun φ : B →ₐ[k] k => φ b) hR
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] at ha hb
  rw [ofConv_toConv, Algebra.TensorProduct.productMap_apply_tmul, ← ha, ← hb, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

@[expose] def tensorPointMulEquiv :
    WithConv (A ⊗[k] B →ₐ[k] k) ≃* WithConv (A →ₐ[k] k) × WithConv (B →ₐ[k] k) :=
  MulEquiv.symm
    { toFun p := toConv (tensorPointEquiv (p.1.ofConv, p.2.ofConv))
      invFun y := (toConv (tensorPointEquiv.symm y.ofConv).1,
        toConv (tensorPointEquiv.symm y.ofConv).2)
      left_inv p := by
        simp only [Equiv.symm_apply_apply, toConv_ofConv]
      right_inv y := by
        simp only [Prod.mk.eta, Equiv.apply_symm_apply, toConv_ofConv]
      map_mul' p q := (productMap_convMul p.1 q.1 p.2 q.2).symm }

theorem tensorPointMulEquiv_symm_apply (p : WithConv (A →ₐ[k] k)) (q : WithConv (B →ₐ[k] k)) :
    (tensorPointMulEquiv.symm (p, q)).ofConv = tensorPointEquiv (p.ofConv, q.ofConv) :=
  rfl

theorem tensorPointMulEquiv_apply (y : WithConv (A ⊗[k] B →ₐ[k] k)) :
    ((tensorPointMulEquiv y).1.ofConv, (tensorPointMulEquiv y).2.ofConv) =
      tensorPointEquiv.symm y.ofConv :=
  rfl

@[simp] theorem tensorPointMulEquiv_apply_fst (y : WithConv (A ⊗[k] B →ₐ[k] k)) :
    (tensorPointMulEquiv y).1.ofConv = y.ofConv.comp Algebra.TensorProduct.includeLeft :=
  rfl

@[simp] theorem tensorPointMulEquiv_apply_snd (y : WithConv (A ⊗[k] B →ₐ[k] k)) :
    (tensorPointMulEquiv y).2.ofConv = y.ofConv.comp Algebra.TensorProduct.includeRight :=
  rfl

end CFSG.LieType.AlgebraicGroups

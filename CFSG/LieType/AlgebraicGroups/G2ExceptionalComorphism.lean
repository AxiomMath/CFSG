module

public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramComorphism
public import CFSG.LieType.AlgebraicGroups.HopfTensorPoints
public import Mathlib.Algebra.DualNumber
import TauCeti.RingTheory.TensorProduct.PointSeparation
import TauCeti.RingTheory.FiniteType.PointSeparation

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct WithConv

section Lift

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [Algebra k A] {D : Type}
  [CommRing D] [Algebra k D] [Algebra.FiniteType k D] [IsReduced D]

theorem map_eq_zero_of_comp_mem (S : Set (A →ₐ[k] k)) (f : A →ₐ[k] D)
    (hf : ∀ z : D →ₐ[k] k, z.comp f ∈ S) {a : A} (ha : a ∈ pointsIdeal S) : f a = 0 :=
  eq_zero_of_forall_algHom k D _ fun z => mem_pointsIdeal.1 ha _ (hf z)

@[expose] def liftOfPoints (S : Set (A →ₐ[k] k)) (f : A →ₐ[k] D)
    (hf : ∀ z : D →ₐ[k] k, z.comp f ∈ S) : (A ⧸ pointsIdeal S) →ₐ[k] D :=
  Ideal.Quotient.liftₐ _ f fun _ ha => map_eq_zero_of_comp_mem S f hf ha

theorem liftOfPoints_comp_mkₐ (S : Set (A →ₐ[k] k)) (f : A →ₐ[k] D)
    (hf : ∀ z : D →ₐ[k] k, z.comp f ∈ S) :
    (liftOfPoints S f hf).comp (Ideal.Quotient.mkₐ k (pointsIdeal S)) = f :=
  AlgHom.ext fun _ => rfl

theorem liftOfPoints_mk (S : Set (A →ₐ[k] k)) (f : A →ₐ[k] D)
    (hf : ∀ z : D →ₐ[k] k, z.comp f ∈ S) (a : A) :
    liftOfPoints S f hf (Ideal.Quotient.mk (pointsIdeal S) a) = f a :=
  rfl

end Lift

section PointDetection

variable {k : Type*} [Field k] {B B' : Type*} [CommRing B] [HopfAlgebra k B] [CommRing B']
  [HopfAlgebra k B']

theorem productMap_comul_apply (y z : B →ₐ[k] k) (b : B) :
    Algebra.TensorProduct.productMap y z (Coalgebra.comul b) = (toConv y * toConv z).ofConv b := by
  rw [AlgHom.convMul_apply]
  induction Coalgebra.comul (R := k) b with
  | tmul a c => simp
  | add s t hs ht => simp only [map_add, hs, ht]

theorem productMap_tensorMap_apply (y z : B' →ₐ[k] k) (f g : B →ₐ[k] B') (t : B ⊗[k] B) :
    Algebra.TensorProduct.productMap y z (Algebra.TensorProduct.map f g t) =
      Algebra.TensorProduct.productMap (y.comp f) (z.comp g) t := by
  induction t with
  | tmul a c => simp
  | add s t hs ht => simp only [map_add, hs, ht]

variable [IsAlgClosed k] [Algebra.FiniteType k B'] [IsReduced B']

@[expose] def bialgHomOfPointMulTo (φ : B →ₐ[k] B')
    (hφ : ∀ y z : WithConv (B' →ₐ[k] k), toConv ((y * z).ofConv.comp φ) =
      toConv (y.ofConv.comp φ) * toConv (z.ofConv.comp φ)) : B →ₐc[k] B' :=
  BialgHom.ofAlgHom φ
    (by
      have h := hφ 1 1
      rw [mul_one] at h
      have h1 := congrArg ofConv (mul_eq_left.1 h.symm)
      have hunit : (1 : WithConv (B' →ₐ[k] k)).ofConv = Bialgebra.counitAlgHom k B' := by
        rw [AlgHom.convOne_def, ofConv_toConv]
        ext a
        rfl
      rw [hunit] at h1
      exact h1)
    (by
      refine AlgHom.ext fun b => ?_
      rw [← sub_eq_zero]
      apply TauCeti.tensor_eq_zero_of_forall_productMap_eq_zero
        (f := fun y : B' →ₐ[k] k => y) (g := fun z : B' →ₐ[k] k => z)
        (fun a ha => TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
          (x := a) (y := 0) fun y => by simpa using ha y)
        (fun a ha => TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
          (x := a) (y := 0) fun z => by simpa using ha z)
        _
      intro y z
      rw [map_sub, sub_eq_zero, AlgHom.comp_apply, AlgHom.comp_apply,
        Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply, productMap_tensorMap_apply,
        productMap_comul_apply, productMap_comul_apply]
      have h := congrArg (fun w : WithConv (B →ₐ[k] k) => w.ofConv b) (hφ (toConv y) (toConv z))
      simp only [AlgHom.comp_apply] at h
      exact h.symm)

@[simp] theorem coe_bialgHomOfPointMulTo (φ : B →ₐ[k] B')
    (hφ : ∀ y z : WithConv (B' →ₐ[k] k), toConv ((y * z).ofConv.comp φ) =
      toConv (y.ofConv.comp φ) * toConv (z.ofConv.comp φ)) :
    (bialgHomOfPointMulTo φ hφ : B →ₐ[k] B') = φ :=
  rfl

end PointDetection

section QuotientLift

variable {k : Type} [Field k] {A B' : Type} [CommRing A] [Bialgebra k A] [CommRing B']
  [Bialgebra k B']

@[expose] def bialgHomQuotientLift (I : Ideal A) [(I.restrictScalars k).IsCoideal]
    (f : A →ₐc[k] B') (hf : ∀ a ∈ I, f a = 0) : (A ⧸ I) →ₐc[k] B' :=
  have hlift : (Ideal.Quotient.liftₐ I (f : A →ₐ[k] B') hf).comp (Ideal.Quotient.mkₐ k I) =
      (f : A →ₐ[k] B') := AlgHom.ext fun _ => rfl
  BialgHom.ofAlgHom (Ideal.Quotient.liftₐ I (f : A →ₐ[k] B') hf)
    (Ideal.Quotient.algHom_ext k (by
      rw [AlgHom.comp_assoc, hlift, BialgHom.counitAlgHom_comp]
      rfl))
    (Ideal.Quotient.algHom_ext k (by
      have hΔ : (Bialgebra.comulAlgHom k (A ⧸ I)).comp (Ideal.Quotient.mkₐ k I) =
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)).comp
            (Bialgebra.comulAlgHom k A) := AlgHom.ext fun _ => rfl
      rw [AlgHom.comp_assoc, hΔ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, hlift,
        BialgHom.map_comp_comulAlgHom, AlgHom.comp_assoc, hlift]))

theorem bialgHomQuotientLift_mk (I : Ideal A) [(I.restrictScalars k).IsCoideal]
    (f : A →ₐc[k] B') (hf : ∀ a ∈ I, f a = 0) (a : A) :
    bialgHomQuotientLift I f hf (Ideal.Quotient.mk I a) = f a :=
  rfl

end QuotientLift

section Include

variable {k : Type} [Field k] {A B : Type} [CommRing A] [HopfAlgebra k A] [CommRing B]
  [HopfAlgebra k B]

theorem includeLeftBialgHom_apply (a : A) : includeLeftBialgHom k A B a = a ⊗ₜ 1 :=
  DFunLike.congr_fun (coe_includeLeftBialgHom (k := k) (A := A) (B := B)) a

theorem includeRightBialgHom_apply (b : B) : includeRightBialgHom k A B b = 1 ⊗ₜ b :=
  DFunLike.congr_fun (coe_includeRightBialgHom (k := k) (A := A) (B := B)) b

end Include

section Dual

variable {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]

@[expose] def dualTangent (f : B →ₐ[k] DualNumber k) : B →ₗ[k] k :=
  (TrivSqZeroExt.sndHom k k).comp f.toLinearMap

theorem dualTangent_apply (f : B →ₐ[k] DualNumber k) (b : B) : dualTangent f b = (f b).snd :=
  rfl

theorem dualTangent_mem (f : B →ₐ[k] DualNumber k) :
    dualTangent f ∈ tangentSpace k B ((TrivSqZeroExt.fstHom k k k).comp f) := by
  refine mem_tangentSpace.2 fun a b => ?_
  rw [dualTangent_apply, dualTangent_apply, dualTangent_apply, map_mul, TrivSqZeroExt.snd_mul]
  simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

end Dual

section FiniteDim

variable {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]

theorem finiteDimensional_tangentSpace [Algebra.FiniteType k B] (x : B →ₐ[k] k) :
    FiniteDimensional k (TangentSpace k B x) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := B)
  let ev : TangentSpace k B x →ₗ[k] (s → k) :=
    { toFun := fun D b => (D : B →ₗ[k] k) b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro D hD
    refine Subtype.ext (eq_zero_of_mem_tangentSpace_of_adjoin_eq_top hs D.2 fun b hb => ?_)
    exact congrFun hD ⟨b, hb⟩
  exact Module.Finite.of_injective ev hinj

end FiniteDim

section Reindex

variable {k : Type} [Field k] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

@[expose] def glReindex (e : ι ≃ κ) :
    Matrix.GeneralLinearGroup ι k ≃* Matrix.GeneralLinearGroup κ k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k e).toMulEquiv

theorem coe_glReindex (e : ι ≃ κ) (g : Matrix.GeneralLinearGroup ι k) :
    (glReindex e g : Matrix κ κ k) = Matrix.reindex e e (g : Matrix ι ι k) :=
  rfl

theorem glReindex_symm_glReindex (e : ι ≃ κ) (g : Matrix.GeneralLinearGroup ι k) :
    glReindex e.symm (glReindex e g) = g := by
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  simp [coe_glReindex]

@[expose] def glReindexCo (e : ι ≃ κ) : GLCoord k κ →ₐ[k] GLCoord k ι :=
  GLCoord.lift k κ (Matrix.reindex e e (glEntryMatrix k ι)) (glDetInv k ι) (by
    rw [Matrix.det_reindex_self, det_glEntryMatrix_mul_glDetInv])

theorem glReindexCo_glEntry (e : ι ≃ κ) (a b : κ) :
    glReindexCo (k := k) e (glEntry k κ a b) = glEntry k ι (e.symm a) (e.symm b) :=
  GLCoord.lift_glEntry k κ _ _ _ a b

theorem glPointEquiv_symm_comp_glReindexCo (e : ι ≃ κ) (y : GLCoord k ι →ₐ[k] k) :
    glPointEquiv.symm (toConv (y.comp (glReindexCo e))) =
      glReindex e (glPointEquiv.symm (toConv y)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rw [glPointEquiv_symm_apply, coe_glReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    glPointEquiv_symm_apply, ofConv_toConv, ofConv_toConv, AlgHom.comp_apply, glReindexCo_glEntry]

end Reindex

end CFSG.LieType.AlgebraicGroups

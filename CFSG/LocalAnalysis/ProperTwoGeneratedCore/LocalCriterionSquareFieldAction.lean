module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFixedBasis
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.SemidirectProduct

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u v

open scoped MatrixGroups

variable {F : Type u} [Field F] {K : Type v} [Field K]

@[expose] def sl2RingEquiv (sigma : F ≃+* K) : SL(2, F) ≃* SL(2, K) where
  toFun := Matrix.SpecialLinearGroup.map sigma.toRingHom
  invFun := Matrix.SpecialLinearGroup.map sigma.symm.toRingHom
  left_inv h := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv h := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' := (Matrix.SpecialLinearGroup.map sigma.toRingHom).map_mul

@[expose] def sl2FieldAction : RingAut F →* MulAut SL(2, F) where
  toFun := sl2RingEquiv
  map_one' := by
    ext h i j
    rfl
  map_mul' sigma rho := by
    ext h i j
    rfl

@[simp] theorem sl2FieldAction_apply (sigma : RingAut F) (h : SL(2, F)) :
    sl2FieldAction sigma h = Matrix.SpecialLinearGroup.map sigma.toRingHom h := rfl

abbrev Gamma (F : Type u) [Field F] := SL(2, F) ⋊[sl2FieldAction] RingAut F

def linearKernel (F : Type u) [Field F] : Subgroup (Gamma F) :=
  (SemidirectProduct.inl : SL(2, F) →* Gamma F).range

theorem linearKernel_eq_projection_ker :
    linearKernel F = (SemidirectProduct.rightHom : Gamma F →* RingAut F).ker :=
  SemidirectProduct.range_inl_eq_ker_rightHom

@[simp] theorem mem_linearKernel_iff (a : Gamma F) :
    a ∈ linearKernel F ↔ a.right = 1 := by
  rw [linearKernel_eq_projection_ker]
  rfl

def centralizerS (a : Gamma F) : Subgroup SL(2, F) :=
  (Subgroup.centralizer {a}).comap (SemidirectProduct.inl : SL(2, F) →* Gamma F)

@[simp] theorem mem_centralizerS_iff (a : Gamma F) (h : SL(2, F)) :
    h ∈ centralizerS a ↔ (SemidirectProduct.inl h : Gamma F) * a =
      a * SemidirectProduct.inl h := by
  simp [centralizerS, Subgroup.mem_centralizer_iff, eq_comm]

instance finiteRingAut [Finite F] : Finite (RingAut F) :=
  Finite.of_injective (fun sigma : RingAut F => (sigma : F → F))
    (fun _ _ h => RingEquiv.ext (congrFun h))

instance finiteGamma [Finite F] : Finite (Gamma F) :=
  Finite.of_equiv (SL(2, F) × RingAut F) SemidirectProduct.equivProd.symm

def semilinearApply (h : SL(2, F)) (sigma : RingAut F) (v : Fin 2 → F) : Fin 2 → F :=
  Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) F) (fun i => sigma (v i))

theorem semilinearApply_add (h : SL(2, F)) (sigma : RingAut F) (v w : Fin 2 → F) :
    semilinearApply h sigma (v + w) =
      semilinearApply h sigma v + semilinearApply h sigma w := by
  ext i
  simp [semilinearApply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem semilinearApply_smul (h : SL(2, F)) (sigma : RingAut F) (c : F) (v : Fin 2 → F) :
    semilinearApply h sigma (c • v) = sigma c • semilinearApply h sigma v := by
  ext i
  simp [semilinearApply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem semilinearApply_involutive (h : SL(2, F)) (sigma : RingAut F)
    (hsigma : sigma ^ 2 = 1) (hh : h * sl2FieldAction sigma h = 1) :
    Function.Involutive (semilinearApply h sigma) := by
  intro v
  have hmat : (h : Matrix (Fin 2) (Fin 2) F) *
      sigma.toRingHom.mapMatrix (h : Matrix (Fin 2) (Fin 2) F) = 1 :=
    congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hh
  have hmap (j : Fin 2) :
      sigma (Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) F)
        (fun k => sigma (v k)) j) =
      Matrix.mulVec (sigma.toRingHom.mapMatrix (h : Matrix (Fin 2) (Fin 2) F)) v j := by
    simpa [Function.comp_def, field_involution_apply sigma hsigma] using
      sigma.toRingHom.map_mulVec (h : Matrix (Fin 2) (Fin 2) F) (fun k => sigma (v k)) j
  unfold semilinearApply
  simp_rw [hmap]
  rw [Matrix.mulVec_mulVec, hmat, Matrix.one_mulVec]

def semilinearInvolution (h : SL(2, F)) (sigma : RingAut F)
    (hsigma : sigma ^ 2 = 1) (hh : h * sl2FieldAction sigma h = 1) :
    (Fin 2 → F) ≃+ (Fin 2 → F) where
  toFun := semilinearApply h sigma
  invFun := semilinearApply h sigma
  left_inv := semilinearApply_involutive h sigma hsigma hh
  right_inv := semilinearApply_involutive h sigma hsigma hh
  map_add' := semilinearApply_add h sigma

theorem outer_involution_cocycle (a : Gamma F) (ha : orderOf a = 2)
    (houter : a ∉ linearKernel F) :
    a.right ≠ 1 ∧ a.right ^ 2 = 1 ∧ a.left * sl2FieldAction a.right a.left = 1 := by
  have hp : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  refine ⟨by simpa using houter, ?_, ?_⟩
  · simpa [pow_two] using congrArg SemidirectProduct.right hp
  · simpa [pow_two] using congrArg SemidirectProduct.left hp

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

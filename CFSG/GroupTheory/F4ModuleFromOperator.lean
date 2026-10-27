module

public import CFSG.GroupTheory.HeisenbergF4FixedDim
public import CFSG.Fischer.Classification.PartII.O2Field
import all CFSG.Fischer.F4

public section

open CFSG.Fischer
open CFSG.GroupTheory.HeisenbergF4

namespace CFSG.GroupTheory.F4ModuleFromOperator

namespace Operator

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem C_apply_sq (C : W →ₗ[ZMod 2] W) (hC : C * C + C + 1 = 0) (v : W) :
    C (C v) = C v + v := by
  have h : C (C v) + C v + v = 0 := by
    simpa using congrArg (fun f : Module.End (ZMod 2) W => f v) hC
  have hz : C v + v + (C v + v) = 0 := by
    rw [← two_smul (ZMod 2) (C v + v)]
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  calc C (C v) = -(C v + v) := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [add_assoc] using h
    _ = C v + v := neg_eq_of_add_eq_zero_left hz

@[expose, instance_reducible] noncomputable def f4Module (C : W →ₗ[ZMod 2] W) (hC : C * C + C + 1 = 0) :
    Module F4 W :=
  Module.compHom W (CFSG.Fischer.Classification.O2Mod.f4End C (C_apply_sq C hC))

theorem f4Module_omega_smul (C : W →ₗ[ZMod 2] W) (hC : C * C + C + 1 = 0) (v : W) :
    letI := f4Module C hC
    F4.ω • v = C v := by
  change CFSG.Fischer.Classification.O2Mod.f4End C (C_apply_sq C hC) F4.ω v = C v
  rw [CFSG.Fischer.Classification.O2Mod.f4End_apply]
  simp [CFSG.Fischer.Classification.O2Mod.F4.re_ω,
    CFSG.Fischer.Classification.O2Mod.F4.im_ω]

section AlgebraMap

local instance : Algebra (ZMod 2) F4 := ZMod.algebra F4 2

theorem F4_re_algebraMap (r : ZMod 2) :
    CFSG.Fischer.Classification.O2Mod.F4.re (algebraMap (ZMod 2) F4 r) = r := by
  revert r
  decide

theorem F4_im_algebraMap (r : ZMod 2) :
    CFSG.Fischer.Classification.O2Mod.F4.im (algebraMap (ZMod 2) F4 r) = 0 := by
  revert r
  decide

theorem f4End_algebraMap (C : W →ₗ[ZMod 2] W) (hC : C * C + C + 1 = 0) (r : ZMod 2) :
    CFSG.Fischer.Classification.O2Mod.f4End C (C_apply_sq C hC)
        (algebraMap (ZMod 2) F4 r) =
      algebraMap (ZMod 2) (Module.End (ZMod 2) W) r := by
  ext v
  rw [CFSG.Fischer.Classification.O2Mod.f4End_apply,
    F4_re_algebraMap, F4_im_algebraMap, zero_smul, add_zero]
  rw [Algebra.algebraMap_eq_smul_one]
  simp

end AlgebraMap

section Linearity

local instance : Algebra (ZMod 2) F4 := ZMod.algebra F4 2

theorem f4End_apply_commute (C : W →ₗ[ZMod 2] W) (hC : C * C + C + 1 = 0)
    (T : W →ₗ[ZMod 2] W) (hT : T.comp C = C.comp T) (c : F4) (v : W) :
    T (CFSG.Fischer.Classification.O2Mod.f4End C (C_apply_sq C hC) c v) =
      CFSG.Fischer.Classification.O2Mod.f4End C (C_apply_sq C hC) c (T v) := by
  rw [CFSG.Fischer.Classification.O2Mod.f4End_apply,
    CFSG.Fischer.Classification.O2Mod.f4End_apply]
  rw [map_add, map_smul, map_smul]
  have h := congrArg (fun f : W →ₗ[ZMod 2] W => f v) hT
  simp only [LinearMap.comp_apply] at h
  rw [h]

theorem isScalarTower_f4Module (C : W →ₗ[ZMod 2] W) (hC : C * C + C + 1 = 0) :
    letI : Algebra (ZMod 2) F4 := ZMod.algebra F4 2
    letI := f4Module C hC
    IsScalarTower (ZMod 2) F4 W := by
  letI : Algebra (ZMod 2) F4 := ZMod.algebra F4 2
  letI := f4Module C hC
  refine ⟨fun r s v => ?_⟩
  change CFSG.Fischer.Classification.O2Mod.f4End C (C_apply_sq C hC)
      (algebraMap (ZMod 2) F4 r * s) v =
    r • (CFSG.Fischer.Classification.O2Mod.f4End C (C_apply_sq C hC) s v)
  rw [map_mul, Module.End.mul_apply, f4End_algebraMap C hC]
  rw [Algebra.algebraMap_eq_smul_one]
  simp

@[expose] noncomputable def f4LinearMap (C : W →ₗ[ZMod 2] W) (hC : C * C + C + 1 = 0)
    (T : W →ₗ[ZMod 2] W) (hT : T.comp C = C.comp T) :=
  letI := f4Module C hC
  ({ toFun := T
     map_add' := T.map_add
     map_smul' := fun c v => by
       change T (CFSG.Fischer.Classification.O2Mod.f4End C (C_apply_sq C hC) c v) =
         CFSG.Fischer.Classification.O2Mod.f4End C (C_apply_sq C hC) c (T v)
       exact f4End_apply_commute C hC T hT c v } : W →ₗ[F4] W)

@[expose] noncomputable def f4LinearEquiv (C : W →ₗ[ZMod 2] W) (hC : C * C + C + 1 = 0)
    (e : W ≃ₗ[ZMod 2] W)
    (he : e.toLinearMap.comp C = C.comp e.toLinearMap) :=
  letI := f4Module C hC
  ({ toLinearMap := f4LinearMap C hC e.toLinearMap he
     invFun := e.symm
     left_inv := e.left_inv
     right_inv := e.right_inv } : W ≃ₗ[F4] W)

end Linearity

end Operator

end CFSG.GroupTheory.F4ModuleFromOperator


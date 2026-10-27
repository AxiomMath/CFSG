module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4F

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag BS4
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] noncomputable def bvGL : GL (Fin 4) F →* GL (Fin 2 ⊕ Fin 2) F :=
  Units.map (bv : Matrix (Fin 4) (Fin 4) F ≃ₐ[F] _).toMonoidHom

theorem coe_bvGL (x : GL (Fin 4) F) :
    ((bvGL x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      bv (x : Matrix (Fin 4) (Fin 4) F) := rfl

theorem bvGL_injective : Function.Injective (bvGL : GL (Fin 4) F →* GL (Fin 2 ⊕ Fin 2) F) :=
  fun _ _ h => Units.ext (bv.injective (congrArg Units.val h))

theorem eig_of_conj {G A : GL (Fin 4) F} {ν : F} {v : Fin 4 → F}
    (h : (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (A : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)) *ᵥ v = ν • v) :
    (A : Matrix (Fin 4) (Fin 4) F) *ᵥ ((G : Matrix (Fin 4) (Fin 4) F) *ᵥ v) =
      ν • ((G : Matrix (Fin 4) (Fin 4) F) *ᵥ v) := by
  have hGG : (G : Matrix (Fin 4) (Fin 4) F) * ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (A : Matrix (Fin 4) (Fin 4) F) *ᵥ ((G : Matrix (Fin 4) (Fin 4) F) *ᵥ v)
      = ((G : Matrix (Fin 4) (Fin 4) F) * (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (A : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F))) *ᵥ v := by
        rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
    _ = ν • ((G : Matrix (Fin 4) (Fin 4) F) *ᵥ v) := by rw [← mulVec_mulVec, h, mulVec_smul]

theorem roweig_of_conj {G A : GL (Fin 4) F} {ν : F} {v : Fin 4 → F}
    (h : v ᵥ* (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (A : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)) = ν • v) :
    (v ᵥ* ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) ᵥ* (A : Matrix (Fin 4) (Fin 4) F) =
      ν • (v ᵥ* ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
  have hGG : (G : Matrix (Fin 4) (Fin 4) F) * ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (v ᵥ* ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) ᵥ* (A : Matrix (Fin 4) (Fin 4) F)
      = v ᵥ* ((((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (A : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)) *
          ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
        rw [vecMul_vecMul, Matrix.mul_assoc _ (G : Matrix (Fin 4) (Fin 4) F), hGG, Matrix.mul_one]
    _ = ν • (v ᵥ* ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
        rw [← vecMul_vecMul, h, smul_vecMul]

theorem mulVec_ne_zero {G : GL (Fin 4) F} {v : Fin 4 → F} (hv : v ≠ 0) :
    (G : Matrix (Fin 4) (Fin 4) F) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (fun w => ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ w) h
  simpa [mulVec_mulVec, ← Units.val_mul] using this

theorem vecMul_ne_zero {G : GL (Fin 4) F} {v : Fin 4 → F} (hv : v ≠ 0) :
    v ᵥ* (G : Matrix (Fin 4) (Fin 4) F) ≠ 0 := by
  intro h
  apply hv
  have := congrArg (fun w => w ᵥ* ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h
  simpa [vecMul_vecMul, ← Units.val_mul] using this

theorem ee0_ne_zero : (ee0 : Fin 4 → F) ≠ 0 := by
  intro h
  simpa using congrFun h 0

theorem ee3_ne_zero : (ee3 : Fin 4 → F) ≠ 0 := by
  intro h
  simpa using congrFun h 3

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

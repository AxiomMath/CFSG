module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4F3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag BS4
open scoped commutatorElement

variable {F : Type} [Field F]

theorem bv_transpose (M : Matrix (Fin 4) (Fin 4) F) : bv Mᵀ = (bv M)ᵀ := rfl

theorem det_bv (M : Matrix (Fin 4) (Fin 4) F) : (bv M).det = M.det := by
  simp only [bv, Matrix.coe_reindexAlgEquiv, det_reindex_self]

theorem comm_of_map {G₁ G₂ : Type*} [Group G₁] [Group G₂] {φ : G₁ →* G₂}
    (hφ : Function.Injective φ) {H : Subgroup G₁}
    (h : ∀ z ∈ ⁅H.map φ, H.map φ⁆, ∀ w ∈ ⁅H.map φ, H.map φ⁆, z * w = w * z) :
    ∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z := by
  have hmc : ⁅H.map φ, H.map φ⁆ = ⁅H, H⁆.map φ := (Subgroup.map_commutator H H φ).symm
  intro z hz w hw
  apply hφ
  rw [map_mul, map_mul]
  exact h _ (hmc ▸ ⟨z, hz, rfl⟩) _ (hmc ▸ ⟨w, hw, rfl⟩)

@[expose] noncomputable def cbv (P : GL (Fin 4) F) : GL (Fin 4) F →* GL (Fin 2 ⊕ Fin 2) F :=
  bvGL.comp (MulAut.conj P⁻¹).toMonoidHom

theorem coe_cbv (P x : GL (Fin 4) F) : ((cbv P x : GL (Fin 2 ⊕ Fin 2) F) : MB F) =
    bv (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) *
      (P : Matrix (Fin 4) (Fin 4) F)) := by
  simp only [cbv, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    coe_bvGL, Units.val_mul]

theorem cbv_injective (P : GL (Fin 4) F) : Function.Injective (cbv P) :=
  bvGL_injective.comp (MulAut.conj P⁻¹).injective

theorem transpose_conj_mul {P x β : Matrix (Fin 4) (Fin 4) F} {Q : Matrix (Fin 4) (Fin 4) F}
    (hPQ : P * Q = 1) (hx : xᵀ * β * x = β) :
    (Q * x * P)ᵀ * (Pᵀ * β * P) * (Q * x * P) = Pᵀ * β * P := by
  have hQt : Qᵀ * Pᵀ = 1 := by rw [← transpose_mul, hPQ, transpose_one]
  calc (Q * x * P)ᵀ * (Pᵀ * β * P) * (Q * x * P)
      = Pᵀ * xᵀ * (Qᵀ * Pᵀ) * β * (P * Q) * x * P := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = Pᵀ * β * P := by
        rw [hQt, hPQ, Matrix.mul_one, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc xᵀ, ← Matrix.mul_assoc (xᵀ * β), hx]

theorem selfAdj_conj {P B β Q : Matrix (Fin 4) (Fin 4) F} (hPQ : P * Q = 1)
    (hB : Bᵀ * β = β * B) : (Q * B * P)ᵀ * (Pᵀ * β * P) = (Pᵀ * β * P) * (Q * B * P) := by
  have hQt : Qᵀ * Pᵀ = 1 := by rw [← transpose_mul, hPQ, transpose_one]
  calc (Q * B * P)ᵀ * (Pᵀ * β * P) = Pᵀ * (Bᵀ * β) * P := by
        simp only [transpose_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Qᵀ, hQt, Matrix.one_mul]
    _ = (Pᵀ * β * P) * (Q * B * P) := by
        rw [hB]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul]

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

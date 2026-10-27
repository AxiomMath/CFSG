module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Hyp

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def fU (e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2))
    (π : Γ →* (W →ₗ[ZMod 2] W)) : Γ →* (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ :=
  ((matHomN e).comp π).toHomUnits

theorem coe_fU (e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)) (π : Γ →* (W →ₗ[ZMod 2] W)) (γ : Γ) :
    ((fU e π γ : (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
      Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2)) = matOfN e (π γ) := rfl

theorem fU_ker (e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)) (π : Γ →* (W →ₗ[ZMod 2] W)) :
    (fU e π).ker = π.ker := by
  ext γ
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Units.ext_iff, coe_fU, Units.val_one]
  constructor
  · intro h; exact matOfN_injective e (h.trans (matOfN_one e).symm)
  · intro h; rw [h, matOfN_one]

@[expose] noncomputable def TU :
    (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ :=
  ⟨tauM, tauM, tauM_mul_self, tauM_mul_self⟩

theorem coe_TU :
    ((TU : (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
      Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2)) = tauM := rfl

theorem coe_TU_inv :
    (((TU : (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ)⁻¹ :
      (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
      Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2)) = tauM := rfl

section Hyp

variable {π : Γ →* (W →ₗ[ZMod 2] W)} {θ : SL3 →* Γ} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {W₀ V : Submodule (ZMod 2) W}
  {τ : Γ →* Γ} {e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)}

theorem R3bHyp.fU_τ (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9) (γ : Γ) :
    fU e π (τ γ) = TU * fU e π γ * TU⁻¹ := by
  ext1
  rw [Units.val_mul, Units.val_mul, coe_fU, coe_fU, coe_TU, coe_TU_inv, h.mx_τ he]

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaN2

module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLB
public import CFSG.ClassicalInvolution.Q3.TL4D1ML32C

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Matrix

noncomputable def linPart (σ : ↥agl32) : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (exists_aperm_eq σ.2).choose

noncomputable def transPart (σ : ↥agl32) : Fin 3 → ZMod 2 :=
  (exists_aperm_eq σ.2).choose_spec.choose

theorem aperm_linPart (σ : ↥agl32) : aperm (linPart σ) (transPart σ) = σ :=
  (exists_aperm_eq σ.2).choose_spec.choose_spec

theorem aperm_one_zero : aperm 1 0 = 1 := Equiv.ext aapply_one

@[expose] noncomputable def linHom : ↥agl32 →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) where
  toFun := linPart
  map_one' := (aperm_inj ((aperm_linPart 1).trans aperm_one_zero.symm)).1
  map_mul' σ τ := by
    have h := aperm_linPart (σ * τ)
    rw [Subgroup.coe_mul, ← aperm_linPart σ, ← aperm_linPart τ, aperm_mul] at h
    exact (aperm_inj h).1

theorem linHom_apply (σ : ↥agl32) : linHom σ = linPart σ := rfl

theorem linPart_eq {A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)} {b : Fin 3 → ZMod 2}
    {σ : ↥agl32} (h : (σ : Equiv.Perm (Fin 8)) = aperm A b) : linPart σ = A :=
  (aperm_inj ((aperm_linPart σ).trans h)).1

theorem aperm_one_mul_self (v : Fin 3 → ZMod 2) : aperm 1 v * aperm 1 v = 1 := by
  rw [aperm_mul, mul_one, show (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)).1 = 1 from rfl,
    one_mulVec, two_smul_zero, aperm_one_zero]

theorem comm_aperm_trans (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b v : Fin 3 → ZMod 2) :
    aperm A b * aperm 1 v * (aperm A b)⁻¹ * (aperm 1 v)⁻¹ = aperm 1 (A.1 *ᵥ v + v) := by
  rw [inv_eq_of_mul_eq_one_right (aperm_one_mul_self v), aperm_inv, aperm_mul, mul_one,
    aperm_mul, mul_inv_cancel, aperm_mul, one_mul]
  congr 1
  rw [show (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)).1 = 1 from rfl, one_mulVec,
    mulVec_mulVec, mul_inv_val, one_mulVec]
  funext i
  simp only [Pi.add_apply]
  generalize (A.1 *ᵥ v) i = x
  generalize b i = y
  generalize v i = z
  revert x y z
  decide

theorem transvection_facts :
    det3 !![1, 1, 0; 0, 1, 0; 0, 0, 1] = 1 ∧ det3 !![1, 0, 0; 1, 1, 0; 0, 0, 1] = 1 ∧
    det3 !![1, 0, 0; 0, 1, 0; 1, 0, 1] = 1 ∧
    (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ![0, 1, 0] + ![0, 1, 0] =
      Pi.single 0 1 ∧
    (!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ![1, 0, 0] + ![1, 0, 0] =
      Pi.single 1 1 ∧
    (!![1, 0, 0; 0, 1, 0; 1, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ![1, 0, 0] + ![1, 0, 0] =
      Pi.single 2 1 := by
  decide

end CFSG.ClassicalInvolution.Q3.TL4

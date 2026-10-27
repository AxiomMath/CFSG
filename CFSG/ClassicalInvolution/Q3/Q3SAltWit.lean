module

public import CFSG.ClassicalInvolution.Q3.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open Equiv

@[expose] def z0 : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

@[expose] def wit1 : Perm (Fin 8) :=
  (swap 0 1 * swap 2 3) * ((swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5)) *
    (swap 0 1 * swap 2 3)⁻¹

@[expose] def wit2 : Perm (Fin 8) := ((swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5))⁻¹

theorem z0_sq : z0 * z0 = 1 := by decide +kernel

theorem z0_ne_one : z0 ≠ 1 := by decide +kernel

theorem z0_support_card : z0.support.card = 8 := by decide +kernel

theorem z0_sign : Perm.sign z0 = 1 := by decide +kernel

theorem wit1_comm : wit1 * z0 = z0 * wit1 := by decide +kernel

theorem wit2_comm : wit2 * z0 = z0 * wit2 := by decide +kernel

theorem wit1_cube : wit1 ^ 3 = 1 := by decide +kernel

theorem wit2_cube : wit2 ^ 3 = 1 := by decide +kernel

theorem wit_prod_sq : (wit1 * wit2) ^ 2 = 1 := by decide +kernel

theorem wit_prod_ne_one : wit1 * wit2 ≠ 1 := by decide +kernel

theorem wit_prod_ne_z0 : wit1 * wit2 ≠ z0 := by decide +kernel

@[expose] def fin8Equiv (n : ℕ) (h : 8 ≤ n) : Fin 8 ≃ {i : Fin n // i.val < 8} where
  toFun i := ⟨Fin.castLE h i, i.2⟩
  invFun i := ⟨i.1.val, i.2⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Fin.ext rfl)

@[expose] def ext8 (n : ℕ) (h : 8 ≤ n) : Perm (Fin 8) →* Perm (Fin n) :=
  Perm.extendDomainHom (fin8Equiv n h)

theorem ext8_injective (n : ℕ) (h : 8 ≤ n) : Function.Injective (ext8 n h) :=
  Perm.extendDomainHom_injective _

theorem sign_ext8 (n : ℕ) (h : 8 ≤ n) (σ : Perm (Fin 8)) :
    Perm.sign (ext8 n h σ) = Perm.sign σ :=
  Perm.sign_extendDomain σ (fin8Equiv n h)

theorem cycleType_ext8 (n : ℕ) (h : 8 ≤ n) (σ : Perm (Fin 8)) :
    (ext8 n h σ).cycleType = σ.cycleType :=
  Perm.cycleType_extendDomain (fin8Equiv n h)

end CFSG.ClassicalInvolution.Q3

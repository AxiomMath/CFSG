module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SemilinearPm

public section

namespace CFSG.LinearAlgebra

theorem units_map_eq_inv_of_card_four
    {K : Type*} [Field K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : σ ≠ 1) (c : Kˣ) :
    Units.map σ.toMonoidHom c = c⁻¹ := by
  apply Units.ext
  rw [Units.coe_map, Units.val_inv_eq_inv_val]
  change σ (c : K) = (c : K)⁻¹
  rw [CFSG.HardMathSupport.Curtis.UnitaryLevi.ringEquiv_apply_eq_sq_of_card_four hK hσ (c : K)]
  apply eq_inv_of_mul_eq_one_left
  have h3 : (c : K) ^ 3 = 1 := by
    simpa using congrArg Units.val
      (CFSG.HardMathSupport.Curtis.UnitaryLevi.units_pow_three_eq_one_of_card_four hK c)
  calc
    (c : K) ^ 2 * (c : K) = (c : K) ^ 3 := by ring
    _ = 1 := h3

end CFSG.LinearAlgebra

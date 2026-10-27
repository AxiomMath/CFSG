module

public import Mathlib.Algebra.Group.Equiv.Finite
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.CoordinateActions

abbrev D := Fin 3 → Multiplicative (ZMod 3)

@[expose] def u : MulAut D where
  toFun f i := if i = 0 then f 0 * (f 1) ^ 2 else f i
  invFun f i := if i = 0 then f 0 * f 1 else f i
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose] def v : MulAut D where
  toFun f i := if i = 0 then f 0 else if i = 1 then f 2 else (f 1) ^ 2
  invFun f i := if i = 0 then f 0 else if i = 1 then (f 2) ^ 2 else f 1
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose] def w : MulAut D where
  toFun f i := if i = 0 then (f 1) ^ 2 else if i = 1 then (f 0) ^ 2 else (f 2) ^ 2
  invFun f i := if i = 0 then (f 1) ^ 2 else if i = 1 then (f 0) ^ 2 else (f 2) ^ 2
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose] def basis (i : Fin 3) : D :=
  Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3))

theorem basis_repr : ∀ f : D,
    f = basis 0 ^ (Multiplicative.toAdd (f 0)).val *
      basis 1 ^ (Multiplicative.toAdd (f 1)).val *
      basis 2 ^ (Multiplicative.toAdd (f 2)).val := by
  decide +kernel

@[expose] def singer : MulAut D := v ^ 2 * w * u * v⁻¹

theorem singer_pow_thirteen : singer ^ 13 = 1 := by decide +kernel
theorem singer_ne_one : singer ≠ 1 := by decide +kernel

theorem orderOf_singer : orderOf singer = 13 := by
  haveI : Fact (Nat.Prime 13) := ⟨by decide +kernel⟩
  exact orderOf_eq_prime_iff.mpr ⟨singer_pow_thirteen, singer_ne_one⟩

theorem thirteen_dvd_card_of_u_v_w {S : Subgroup (MulAut D)}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) : 13 ∣ Nat.card S := by
  have hs : singer ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem (S.pow_mem hv 2) hw) hu) (S.inv_mem hv)
  have horder : orderOf (⟨singer, hs⟩ : S) = 13 := by
    exact (orderOf_injective S.subtype Subtype.val_injective (⟨singer, hs⟩ : S)).symm.trans
      orderOf_singer
  rw [← horder]
  exact orderOf_dvd_natCard _

end CFSG.LieType.Chevalley.E7Three.CoordinateActions

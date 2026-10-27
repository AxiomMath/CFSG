module

public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Phi (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) :
    S.M →* ((Fin 32 → ZMod 2) ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) where
  toFun g := φ.symm.trans (((S.ρ g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).trans φ)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Subgroup.coe_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

variable {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)}

theorem Phi_apply (g : S.M) (v : Fin 32 → ZMod 2) :
    Phi S φ g v = φ (((S.ρ g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (φ.symm v)) := rfl

theorem Phi_cl (g : S.M) {y : G} (hy : y ∈ S.QG) :
    Phi S φ g (φ (S.cl y)) = φ (S.cl ((g : G) * y * (g : G)⁻¹)) := by
  rw [Phi_apply, LinearEquiv.symm_apply_apply, S.ρ_cl g hy]

end CFSG.GF2Type.SmithTypeE.E7

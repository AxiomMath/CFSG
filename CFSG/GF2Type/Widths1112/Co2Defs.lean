module

public import CFSG.Blueprint.NativeSporadic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112

open CFSG.Blueprint.NativeSporadic

@[expose] noncomputable def co2Act : Representation (ZMod 2) Co2 (Fin 22 → ZMod 2) where
  toFun g := Matrix.mulVecLin (g : Matrix (Fin 22) (Fin 22) (ZMod 2))
  map_one' := by
    simp only [Units.val_one, Submonoid.coe_one, Matrix.mulVecLin_one]
    rfl
  map_mul' g h := by
    simp only [Units.val_mul, Submonoid.coe_mul, Matrix.mulVecLin_mul]
    rfl

@[expose] def Co2ModuleUniqueness : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V], Module.finrank (ZMod 2) V = 22 →
    ∀ ρ : Representation (ZMod 2) Co2 V, Function.Injective ρ →
      ∀ q : QuadraticForm (ZMod 2) V, (QuadraticMap.polarBilin q).Nondegenerate →
        (∀ g v, q (ρ g v) = q v) →
          ∃ ψ : V ≃ₗ[ZMod 2] (Fin 22 → ZMod 2), ∀ g v, ψ (ρ g v) = co2Act g (ψ v)

end CFSG.GF2Type.Widths1112

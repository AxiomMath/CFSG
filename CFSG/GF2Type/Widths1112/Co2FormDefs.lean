module

public import CFSG.GF2Type.Widths1112.Co2Setup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2.Native
  CFSG.GF2W1112 Matrix

@[expose] noncomputable def Qm22 : Matrix (Fin 22) (Fin 22) (ZMod 2) := rowsMatrix 22 w12Co2QRows

@[expose] noncomputable def q₀₂ (v : Vec22) : ZMod 2 := v ⬝ᵥ (Qm22 *ᵥ v)

@[expose] noncomputable def bil₀₂ (u v : Vec22) : ZMod 2 := u ⬝ᵥ ((Qm22 + Qm22ᵀ) *ᵥ v)

@[expose] def co2Orbit (i : ℕ) : Set Vec22 :=
  Set.range fun g : NativeSporadic.Co2 => co2Act g (toVecD 22 (w12Co2Rep i))

end CFSG.GF2Type.Widths1112

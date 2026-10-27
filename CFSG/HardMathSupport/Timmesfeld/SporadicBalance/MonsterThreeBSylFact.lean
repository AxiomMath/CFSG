module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBLocal

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open _root_.Timmesfeld.M3B (tMats)

section Datum


@[expose] def SylFact : Prop :=
  ∃ S : Subgroup (GL (Fin 12) (ZMod 3)), S ≤ rhoL.range ∧ Nat.card S = 3 ^ 7 ∧
    ∀ y ∈ S, y ^ 3 = 1 → y ≠ 1 → ∃ g : tbL, ∃ j < 3,
      (((rhoL g)⁻¹ * y * rhoL g : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)) =
        toMatrix (tMats ())[j]!

end Datum

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

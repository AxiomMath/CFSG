module

public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.Generated.Data
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterInversion
public import CFSG.Monster.GMS.Defs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.Generated
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

@[expose] def B3BLeaf : Prop :=
  ∀ x : NativeSporadic.B, orderOf x = 3 →
    (∀ d : NativeSporadic.B, BabyInv 0 d → d * x * d⁻¹ ≠ x⁻¹) →
      ¬ 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set NativeSporadic.B))

end CFSG.HardMathSupport.Dickson.Sec6.BM

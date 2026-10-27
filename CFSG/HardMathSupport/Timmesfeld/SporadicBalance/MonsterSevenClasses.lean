module

public import CFSG.Monster.Generated.Data

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

@[expose] def MonsterSevenClasses (a b : CFSG.Monster.Generated.Gmat) : Prop :=
  ∀ s : CFSG.Monster.Generated.Gmat, orderOf s = 7 → IsConj s a ∨ IsConj s b

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance

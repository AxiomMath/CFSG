module

public import CFSG.HardMathSupport.Lang.E6Descent.SylowCore
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.MaxClassTStar

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

theorem rankBoundTStar : RankBoundTStar := fun Q _ _ hQ x hx3 hCx M _ hMi hxM hM81 E hEM hE =>
  CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.card_elemAbelian_lt_27 hQ hx3 hCx hMi hxM hM81
    hEM hE

end CFSG.HardMathSupport.Lang.E6Descent

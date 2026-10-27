module

public import Certificates.Data.TabMSevenHe
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeADenseInputs

public section

namespace CFSG.KC.KDenseP.HeSeven

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.HardMathSupport.Dickson.I271.TabMSeven
  CFSG.HardMathSupport.Dickson.I271.TabMThreeA

abbrev Prs := List (List Native.Gen × List Native.Gen)

@[expose] def tri (eqs nes : Prs) : Prs := eqs ++ eqs ++ eqs ++ nes

@[expose] def eHe : Prs := (heWordList ()).map fun w => (w, [])

@[expose] def nHe : Prs := [(heA, []), (powL 17 denseZWord ++ tWord, powL 17 denseZWord)]

end CFSG.KC.KDenseP.HeSeven

end

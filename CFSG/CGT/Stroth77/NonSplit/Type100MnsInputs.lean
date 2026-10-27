module

public import CFSG.CGT.Stroth77.NonSplit.StrothTInputs
public import CFSG.CGT.Stroth77.Types

public section

namespace CFSG.CGT.Stroth77

@[expose] def toA (x : Torus (Type100.k 1)) : Mns :=
  mnsW ^ (x 0).val * (mnsX1 * mnsX) ^ (x 1).val * (mnsY1 * mnsY) ^ (x 2).val

end CFSG.CGT.Stroth77

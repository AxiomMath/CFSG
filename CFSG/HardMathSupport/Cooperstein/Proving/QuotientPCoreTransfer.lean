module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

noncomputable def quotientPCoreMulEquiv {H K : Type} [Group H] [Group K] (p : ℕ) (e : H ≃* K) :
    (H ⧸ CFSG.pCore p H) ≃* (K ⧸ CFSG.pCore p K) :=
  QuotientGroup.congr _ _ e (CFSG.pCore_map_iso p e)

end CFSG.HardMathSupport.Cooperstein.Proving

end

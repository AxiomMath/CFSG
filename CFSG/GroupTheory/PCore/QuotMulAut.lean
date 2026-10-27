module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG

@[expose] noncomputable def pCoreQuotMulAut (H : Type*) [Group H] :
    MulAut H →* MulAut (H ⧸ CFSG.pCore 2 H) where
  toFun σ := QuotientGroup.congr _ _ σ (CFSG.pCore_map_iso 2 σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem pCoreQuotMulAut_mk {H : Type*} [Group H] (σ : MulAut H) (x : H) :
    pCoreQuotMulAut H σ (x : H ⧸ CFSG.pCore 2 H) =
      ((σ x : H) : H ⧸ CFSG.pCore 2 H) :=
  rfl

end CFSG

end

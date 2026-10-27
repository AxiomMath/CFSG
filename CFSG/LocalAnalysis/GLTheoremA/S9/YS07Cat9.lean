module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat8
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93All

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section YS07Cat9

theorem ys07_of_cat9_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S9Cat8Inputs G p) : YS07 :=
  ys07_of_cat8_inputs List93.i9List93Residual_holds hin

end YS07Cat9

end CFSG.LocalAnalysis.GLTheoremA

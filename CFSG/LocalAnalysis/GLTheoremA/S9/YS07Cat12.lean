module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat11
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269R6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys07Cat12

theorem ys07_of_cat12_inputs
    (hD : D4XF.D4TwoAutNormInn) (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ),
    ThmACtx G m → ∀ p ∈ Mu G m, S9Cat11Inputs G p) : YS07 :=
  ys07_of_cat11_inputs ⟨i269Residual3_holds, hD⟩ hin

end Ys07Cat12

end CFSG.LocalAnalysis.GLTheoremA

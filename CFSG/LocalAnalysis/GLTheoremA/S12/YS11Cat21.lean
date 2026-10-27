module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat20
public import CFSG.HardMathSupport.Dickson.BMRows.M11Rows
public import CFSG.HardMathSupport.Dickson.BMRows.M11Holds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

section Ys11Cat21

theorem ys11_of_cat21_inputs
    (hT : ∀ f : ℕ, 1 ≤ f → TD4InnThreeCentLe f) (hR : I1429Residual)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat20Inputs G p ∧ S12CanonInputs G p) : YS11 :=
  ys11_of_cat20_inputs (CFSG.HardMathSupport.Dickson.BMRows.row_M_eleven CFSG.HardMathSupport.Dickson.BMRows.M11.centElevenBound_holds) hT hR hin

end Ys11Cat21

end CFSG.LocalAnalysis.GLTheoremA

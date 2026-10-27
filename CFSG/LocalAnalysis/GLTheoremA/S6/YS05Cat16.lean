module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKChainYS05b
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKI1415K
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKNineK
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKAltK
public import CFSG.HardMathSupport.Dickson.BMRows.KFormRowsBM
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FRes

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.BMRows (I1416QSporSK i1416At_of_sporK)

section Ys05Cat16


theorem ys05_of_cat16_inputs
    (hM11 : I1416QRows.I1416QRow .M 11) (hR : D3Residual)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
      ∀ p ∈ Mu G m, S6Cat14Inputs G p) : YS05 :=
  ys05_of_cat14K
    ⟨CFSG.HardMathSupport.Dickson.BMRows.i1416QSporSK_of_rows hM11, i1415SporSK_holds, i1415NineSporSK_holds,
      i1415SevenSporSK_holds, i1422SporSK_holds⟩ (d3Facts_of_residual hR) h

end Ys05Cat16

end CFSG.LocalAnalysis.GLTheoremA

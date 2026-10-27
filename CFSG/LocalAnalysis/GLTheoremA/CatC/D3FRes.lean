module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Bundle
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FTriality

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure D3Residual : Prop where
  inner : D3InnerInvolution
  field : D3FieldInvolution
  fpf : D3FixedPointFree

section D3FRes

theorem d3Facts_of_residual
    (h : D3Residual) : D3Facts :=
  ⟨d3TrialityCentRank_holds, h.inner, h.field, h.fpf⟩

theorem ys04_of_residual
    (h : D3Residual) : YS04 :=
  ys04_of_d3Facts (d3Facts_of_residual h)

end D3FRes

end CFSG.LocalAnalysis.GLTheoremA

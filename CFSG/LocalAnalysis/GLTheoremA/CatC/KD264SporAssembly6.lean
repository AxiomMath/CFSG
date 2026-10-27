module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAssembly5
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporCo15

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint

@[expose] def KD264SporResidual6 : Prop := KD264SporAt 7 .B ∧ KD264SporAt 3 .Co1

section Rows

theorem kd264SporResidual5_of_residual6 (h : KD264SporResidual6) : KD264SporResidual5 :=
  ⟨h.1, h.2,
    Co15.kd264SporAt_Co1_five CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds⟩

theorem kd264SporS_of_residual6 (h : KD264SporResidual6) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    KD264SporS p :=
  kd264SporS_of_residual5 (kd264SporResidual5_of_residual6 h) p hp hp2

end Rows

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen

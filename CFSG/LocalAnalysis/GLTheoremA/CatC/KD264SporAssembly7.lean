module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAssembly6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporCo13

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint

section Rows

theorem kd264SporResidual6_of_B7 (h : KD264SporAt 7 .B) : KD264SporResidual6 :=
  ⟨h, Co13.kd264SporAt_Co1_three CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds⟩

theorem kd264SporS_of_B7 (h : KD264SporAt 7 .B) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    KD264SporS p :=
  kd264SporS_of_residual6 (kd264SporResidual6_of_B7 h) p hp hp2

end Rows

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen

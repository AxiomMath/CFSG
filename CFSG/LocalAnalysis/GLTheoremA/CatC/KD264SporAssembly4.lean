module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAssembly3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporCo17

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint

@[expose] def KD264SporResidual4 : Prop :=
  KD264SporAt 7 .B ∧ KD264SporAt 3 .Co1 ∧ KD264SporAt 5 .Co1 ∧ KD264SporAt 3 .HN

section Rows

theorem kd264SporResidual3_of_residual4 (h : KD264SporResidual4) : KD264SporResidual3 :=
  ⟨h.1, h.2.1, h.2.2.1,
    kd264SporAt_Co1_seven CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds, h.2.2.2,
    kd264SporAt_Th_seven CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds⟩

theorem kd264SporS_of_residual4 (h : KD264SporResidual4) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    KD264SporS p :=
  kd264SporS_of_residual3 (kd264SporResidual3_of_residual4 h) p hp hp2

end Rows

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen

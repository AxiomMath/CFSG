module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAssembly4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporHN3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint

@[expose] def KD264SporResidual5 : Prop :=
  KD264SporAt 7 .B ∧ KD264SporAt 3 .Co1 ∧ KD264SporAt 5 .Co1

section Rows

theorem kd264SporResidual4_of_residual5 (h : KD264SporResidual5) : KD264SporResidual4 :=
  ⟨h.1, h.2.1, h.2.2,
    HN3.kd264SporAt_HN_three CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds⟩

theorem kd264SporS_of_residual5 (h : KD264SporResidual5) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    KD264SporS p :=
  kd264SporS_of_residual4 (kd264SporResidual4_of_residual5 h) p hp hp2

end Rows

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen

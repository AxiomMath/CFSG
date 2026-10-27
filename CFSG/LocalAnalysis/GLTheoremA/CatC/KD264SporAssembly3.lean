module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporM
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAssembly2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def KD264SporResidual3 : Prop :=
  KD264SporAt 7 .B ∧ KD264SporAt 3 .Co1 ∧ KD264SporAt 5 .Co1 ∧ KD264SporAt 7 .Co1 ∧
    KD264SporAt 3 .HN ∧ KD264SporAt 7 .Th

section Rows

theorem kd264SporResidual2_of_residual3 (h : KD264SporResidual3) : KD264SporResidual2 :=
  ⟨fun _ hp hp2 => kd264SporAt_M hp hp2, h⟩

theorem kd264SporS_of_residual3 (h : KD264SporResidual3) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    KD264SporS p :=
  kd264SporS_of_residual2 CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group sporadicOrdersTable_holds
    CFSG.Sporadic.Bridge.carrier_finite_simple_of_ne_M (kd264SporResidual2_of_residual3 h) p hp
    hp2

end Rows

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen

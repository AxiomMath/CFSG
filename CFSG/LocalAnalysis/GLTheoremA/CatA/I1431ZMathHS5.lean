module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB3
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM3
public import CFSG.HardMathSupport.Dickson.BMRows.RowsB
public import CFSG.HardMathSupport.Dickson.BMRows.RowsM

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Z

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.Blueprint.NativeSporadic (Carrier)


theorem row_B_of_kGroup
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : I1431SporRow .B := by
  obtain ⟨hfin, hs, ⟨b⟩, hnc⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_B
  refine @row_of_model .B (Carrier .B) _ hfin hs hOut b hnc fun k hk I hI hcI => ?_
  obtain ⟨i, rfl, ⟨e⟩⟩ := CFSG.HardMathSupport.Dickson.BMRows.census_B_three hK k hk I hI
  rw [Nat.card_congr e.toEquiv,
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds .Fi22] at hcI
  exact absurd hcI (by decide)

theorem row_M_of_kGroup
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hK : CFSG.Open.IsKGroup (Carrier .M)) : I1431SporRow .M := by
  obtain ⟨hfin, hs, ⟨b⟩, hnc⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_M
  refine @row_of_model .M (Carrier .M) _ hfin hs hOut b hnc fun k hk I hI hcI => ?_
  obtain ⟨i, hi, ⟨e⟩⟩ := CFSG.HardMathSupport.Dickson.BMRows.census_M_three hK k hk I hI
  rcases hi with rfl | rfl
  · rw [Nat.card_congr e.toEquiv,
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds .Fi24Prime] at hcI
    exact absurd hcI (by decide)
  · rw [Nat.card_congr e.toEquiv,
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds .Th] at hcI
    exact absurd hcI (by decide)

end CFSG.LocalAnalysis.GLTheoremA.I1431Z

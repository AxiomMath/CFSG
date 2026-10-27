module

public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultReduction
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.LocalAnalysis.GLTheoremA

private theorem census_sporadicMultiplierOrder_eq (s : TauCeti.SporadicName) :
    CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s = sporadicMultiplierOrder s := by
  cases s <;> rfl


theorem sporadicMultiplierTable_holds : SporadicMultiplierTable := by
  intro s Q _ _ hQ f hf hker
  have hc : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (TauCeti.CFSGIndex.sporadic s).Group) = sporadicMultiplierOrder s := by
    rw [← census_sporadicMultiplierOrder_eq]
    exact CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds.1 s
  have hd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier (⟨hQ.1⟩ : Group.IsPerfect Q) f hf hker.le
  rw [hker, hc] at hd
  exact hd

end CFSG.LocalAnalysis.GLTheoremA

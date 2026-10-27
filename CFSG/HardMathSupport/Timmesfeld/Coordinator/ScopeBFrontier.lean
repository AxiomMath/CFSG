module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_KernelT
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Kernel116TDefs
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Quat
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem sporadicMultipliers_of_census
    (h : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    Tables.Multiplier.SporadicMultipliers :=
  ⟨fun s => by rw [h.1 s]; cases s <;> rfl, h.2⟩

theorem kernelT_of_kernel11_6T (h : Kernel11_6T) : KernelT := by
  intro J _ _ hq hK p hp hp2 hU φ hφ
  obtain ⟨x, hx⟩ := h J hq hK p hp hp2 hU φ hφ
  exact ⟨x, fun t => by rw [hx]; rfl⟩

end CFSG.HardMathSupport.Timmesfeld.Coordinator

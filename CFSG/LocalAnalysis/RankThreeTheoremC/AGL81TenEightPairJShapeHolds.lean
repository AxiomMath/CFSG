module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightPairJShapeOf
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

section He


theorem he_isSimpleGroup_and_card :
    IsSimpleGroup TauCeti.SporadicName.He.Group ∧
      Nat.card TauCeti.SporadicName.He.Group = 4030387200 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm, ?_⟩
  have h := Nat.card_congr e.toEquiv
  rw [CFSG.Sporadic.He.card_He] at h
  exact h.symm

end He

section Main

theorem kFactThreeFourPairJShape_holds : KFactThreeFourPairJShape :=
  kFactThreeFourPairJShape_of CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.lie_char_part he_isSimpleGroup_and_card

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

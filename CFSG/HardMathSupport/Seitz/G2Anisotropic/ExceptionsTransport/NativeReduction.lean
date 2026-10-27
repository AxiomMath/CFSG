module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.A1A1Overgroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.SEITZ3

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

theorem finite_adjointGroup_G2 (K : Type) [Field K] [Finite K] : Finite (adjointGroup .G2 K) := by
  have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  refine Nat.finite_of_card_ne_zero ?_
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, ordG2_closed _ (by omega)]
  have : 0 < Nat.card K ^ 2 - 1 := by
    have : 4 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  positivity

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

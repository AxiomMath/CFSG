module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOne
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCarrierSimple
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenPair

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Blueprint

theorem sporadicBMData_holds
    : Tables.Census.SporadicBMData := by
  refine ⟨CFSG.Monster.Existence.card_nativeB, ?_, ?_⟩
  · rw [show Nat.card (NativeSporadic.Carrier .M) = Nat.card CFSG.Open.MonsterY443Derived from
      Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv]
    exact CFSG.Milestones.fam_m_finiteness
  · have : IsSimpleGroup (NativeSporadic.Carrier .M) :=
      CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
    obtain ⟨e⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
      (T := NativeSporadic.Carrier .M) (MulEquiv.refl _)
    exact CFSG.AGLEmbedding.Norton.MON11_13.hasNoncommPair_thirteen_of_mulEquiv_Gmat e

end CFSG.HardMathSupport.Timmesfeld.Coordinator

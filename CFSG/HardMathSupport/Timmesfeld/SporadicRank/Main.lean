module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.McL
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Suz
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi22
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi24
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicCoverReduce

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem sporadicBigCoverRank_of_groups (hSpM : Tables.Multiplier.SporadicMultipliers)
    (hMcL : BigCoverRankAt .McL) (hSuz : BigCoverRankAt .Suz) (hFi22 : BigCoverRankAt .Fi22)
    (hFi24 : BigCoverRankAt .Fi24Prime) : SporadicBigCoverRank := by
  intro L _ _ hq s hs ⟨e⟩ h3
  have hdvd := card_center_dvd_sporadicMultiplierOrder hSpM hq s e
  have h6 : Nat.card (Subgroup.center L) ∣ 6 := by
    refine hdvd.trans ?_
    rcases hs with rfl | rfl | rfl | rfl <;> simp [Tables.Multiplier.sporadicMultiplierOrder]
  rcases hs with rfl | rfl | rfl | rfl
  · exact hMcL L hq ⟨e⟩ h6 h3
  · exact hSuz L hq ⟨e⟩ h6 h3
  · exact hFi22 L hq ⟨e⟩ h6 h3
  · exact hFi24 L hq ⟨e⟩ h6 h3

theorem sporadicBigCoverRank_holds
    (hSpM : Tables.Multiplier.SporadicMultipliers) :
    SporadicBigCoverRank :=
  sporadicBigCoverRank_of_groups hSpM bigCoverRankAt_McL bigCoverRankAt_Suz bigCoverRankAt_Fi22
    bigCoverRankAt_Fi24

end CFSG.HardMathSupport.Timmesfeld.SporadicRank

module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicRankData

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance

theorem tables112Types_TON_rank_holds :
    ∀ (K : Type) [Group K] [Finite K], IsHatON K → 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  rintro K _ _ ⟨-, hc, ⟨e⟩⟩
  have h4 := sporadicThreeRankGe_ONan (K ⧸ Subgroup.center K) ⟨e⟩
  have h3 := pRank_centerQuotient_le_of_center (L := K) Nat.prime_three (by norm_num)
    (by rw [hc]) (by rw [hc]; norm_num)
  omega

end CFSG.HardMathSupport.Solomon.Coordinator

module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicRankCommData
import CFSG.Monster.B.Pinned.Primes.FiveSubgroup
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.Monster.B.Pinned

theorem three_le_pRank_B_five :
    3 ≤ Open.pRank 5 (⊤ : Subgroup (NativeSporadic.Carrier .B)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite NativeSporadic.B := finite_carrier_B
  exact three_le_pRank_of_commData (G := NativeSporadic.B) commData_five (i := 1) (j := 2)
    (by decide) rfl

end CFSG.AGLEmbedding

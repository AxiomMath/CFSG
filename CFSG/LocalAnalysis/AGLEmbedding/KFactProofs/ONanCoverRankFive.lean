module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
import CFSG.LocalAnalysis.AGLEmbedding.CoverRankLift
import CFSG.RankThree.PartOne.K159.CenterRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers)
open CFSG.AGLEmbedding.KFactProofs.CoverFive

theorem kFactCoverRankFive_of (hGA : GriessMultipliersAllModels) (hSpor : SporadicMultipliers) :
    KFactCoverRankFive := by
  intro K _ _ hq hcat p hp hp5 hZ hZp
  have hpZ : p ∣ Nat.card (Subgroup.center K) := dvd_card_center_of_isPGroup hp hZ hZp
  have hodd : Odd (Nat.card (Subgroup.center K)) :=
    odd_card_center_of_isPGroup hp (by omega) hZp
  have hrank : ∀ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
      p ^ 4 ≤ Nat.card B → 4 ≤ Open.pRank p (⊤ : Subgroup K) :=
    fun B hBp hBc hBcard =>
      le_pRank_of_pow_le_card hp le_top ⟨⟨⟨fun a b => Subtype.ext (hBc a a.2 b b.2)⟩⟩, hBp⟩ hBcard
  rcases cover_five_classical hGA hSpor hq hcat hp hp5 hZ hZp with
    ⟨n, ℓ, f, hmod, hpn, hpq⟩ | ⟨n, ℓ, f, hmod, hpn, hpq⟩
  · obtain ⟨B, hBp, hBc, hBcard⟩ :=
      CFSG.RankThree.PartOne.K159.exists_elemAbelian_four_psl hp (by omega) hpZ hodd hmod hpn hpq
    exact hrank B hBp hBc hBcard
  · obtain ⟨B, hBp, hBc, hBcard⟩ :=
      CFSG.RankThree.PartOne.K159.exists_elemAbelian_four_psu hp (by omega) hpZ hodd hmod hpn hpq
    exact hrank B hBp hBc hBcard

end CFSG.AGLEmbedding

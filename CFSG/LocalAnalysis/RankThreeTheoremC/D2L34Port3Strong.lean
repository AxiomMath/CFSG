module

import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Reduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

theorem D2ThreeClauseAt.stronglyEmbedded_of_not_isSolvable {G : Type} [Group G] [Finite G]
    {M : Subgroup G} (hb : D2ThreeClauseAt G M) (hS : Setting G) (hM : rankThreeIsMaxTwoLocal M)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} (hMP : IsCoreMaxLocal 3 P M)
    (hns : ¬ Group.IsSolvable M) : GLBStronglyEmbedded 3 M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hS.simple
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hMP
  have hMtop : M ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hM.1
  have hP1 : (P : Subgroup G) ≠ ⊥ := by
    intro h
    obtain ⟨E, hE, -, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3
      Nat.prime_three (P : Subgroup G)
    rw [h, le_bot_iff] at hE
    rw [hE, Subgroup.card_bot, hP3] at hcard
    norm_num at hcard
  have hstr := (CFSG.LocalAnalysis.RankThreeUC.gamma_one_le_iff_isStronglyPEmbedded hPM hMtop
    hP1).mp ((hb hp P hMP).2 hns)
  exact ⟨hstr.1, hstr.2.1, fun g hg hdvd =>
    hstr.2.2 g⁻¹ (fun h' => hg (by simpa using M.inv_mem h')) hdvd⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

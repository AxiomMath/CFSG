module

public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen
public import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem CStarGen.isStronglyPEmbedded_of_not_isSolvable (hC : CStarGen G) {M : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) {d : ℕ} (hd : d ∈ sigmaSet G M) (hd3 : d ≠ 3)
    (hns : ¬ Group.IsSolvable ↥M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded d M := by
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  haveI : Fact d.Prime := ⟨hdp⟩
  obtain ⟨P, hPM, -, hcase⟩ := hC.almost M hM d hd
  haveI : IsSimpleGroup G := hC.simple
  have hMtop : M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hC.nonab M hM.1
  have hd2 : 2 ≤ CFSG.Open.pRank d M := hd.2
  have hdvd : d ∣ Nat.card G :=
    CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos d M (by omega)
  have hP : (P : Subgroup G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hdvd
  rcases hcase with hΓ | hclause2 | hclause3
  · exact
      (CFSG.LocalAnalysis.RankThreeUC.gamma_one_le_iff_isStronglyPEmbedded hPM hMtop hP).mp hΓ
  · exact absurd hclause2.2.1 hns
  · exact absurd hclause3.1 hd3

end CFSG.LocalAnalysis.AGL81TheoremCD

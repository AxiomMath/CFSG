module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitTwistedDPlus

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open


theorem rk2_low_twd_one (K : Type) [Group K] [Finite K] (lab : GLALabel) (hK : Rk2IsLabel K lab)
    (htag : lab.tag = .twD) (hℓ : 4 ≤ lab.rank) (hn : lab.n = 1) :
    lab.rank - 1 ≤ CFSG.Open.evenRank K := by
  have h1 : lab.rank - 1 + CFSG.Open.pRank 3 (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank 3 K :=
    rk2_split_low_twD hK Nat.prime_three (by norm_num) htag hℓ (by rw [hn]; norm_num)
  have h2 : CFSG.Open.twoLocalPrimeRank 3 K ≤ CFSG.Open.evenRank K :=
    CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_evenRank 3 Nat.prime_three
      (by norm_num) K
  omega

end CFSG.LocalAnalysis.GLTheoremA

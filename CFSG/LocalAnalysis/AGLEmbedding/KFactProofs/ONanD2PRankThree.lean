module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankLift
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowSuz
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowONan
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowHNThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowLyThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowTh
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowFi23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowCo1Three
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowFi24

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint CFSG.AGLEmbedding

theorem three_le_pRank_Suz_three
    [Finite (NativeSporadic.Carrier .Suz)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Suz)) :=
  ModuleDatum.three_le_pRank Nat.prime_three (by norm_num) moduleDatum_Suz_three

theorem three_le_pRank_ONan_three
    [Finite (NativeSporadic.Carrier .ONan)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .ONan)) :=
  AbelianSylowDatum.three_le_pRank Nat.prime_three
    (by
      show 3 ^ 3 ∣ Nat.card NativeSporadic.ON
      rw [CFSG.Sporadic.ON.card_ON]
      norm_num)
    abelianSylowDatum_ON_three

theorem three_le_pRank_Fi22_three
    [Finite (NativeSporadic.Carrier .Fi22)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Fi22)) :=
  ModuleDatum.three_le_pRank Nat.prime_three (by norm_num) moduleDatum_Fi22_three

theorem three_le_pRank_HN_three
    [Finite (NativeSporadic.Carrier .HN)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .HN)) :=
  ModuleDatum.three_le_pRank Nat.prime_three (by norm_num) moduleDatum_HN_three

theorem three_le_pRank_Ly_three
    [Finite (NativeSporadic.Carrier .Ly)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Ly)) :=
  ModuleDatum.three_le_pRank Nat.prime_three (by norm_num) moduleDatum_Ly_three

theorem three_le_pRank_Th_three
    [Finite (NativeSporadic.Carrier .Th)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Th)) :=
  ModuleDatum.three_le_pRank Nat.prime_three (by norm_num) moduleDatum_Th_three

theorem three_le_pRank_Fi23_three
    [Finite (NativeSporadic.Carrier .Fi23)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Fi23)) :=
  ModuleDatum.three_le_pRank Nat.prime_three (by norm_num) moduleDatum_Fi23_three

theorem three_le_pRank_Co1_three
    [Finite (NativeSporadic.Carrier .Co1)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Co1)) :=
  ModuleDatum.three_le_pRank Nat.prime_three (by norm_num) moduleDatum_Co1_three

theorem three_le_pRank_Fi24Prime_three
    [Finite (NativeSporadic.Carrier .Fi24Prime)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Fi24Prime)) :=
  ModuleDatum.three_le_pRank Nat.prime_three (by norm_num) moduleDatum_Fi24_three

end CFSG.AGLEmbeddingD2

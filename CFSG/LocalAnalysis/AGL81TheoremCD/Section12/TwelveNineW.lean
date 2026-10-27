module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveEightA9
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KParabolics

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]
variable {M Q H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem hNineW_of_twelveSix (h : TwelveCtx G M p Q H)
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) (h6 : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃)
    (h3 : CFSG.Open.pRank 3 M ≤ 3) (hcard : (weakBlockSet M H).ncard = 3) :
    ∀ D : Subgroup G, IsThreeOnePlusTwo ↥D → D ≤ Q →
      ¬ kSub p M H ⊓ normalizer (D : Set G) ≤ M :=
  fun _ hD hDQ => not_inf_normalizer_le_of_isThreeOnePlusTwo
    (twelveEight_of_twelveSix h hd h6 h3 hcard) (twelveSevenData h hd h6 h3 hcard).2.2.1 hDQ hD
    (TwelveSix.part_six hd h6 Q (isSylowOf_three_inf h hd h6 h3 hcard)).le

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

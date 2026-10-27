module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveKer
public import CFSG.GroupTheory.SylowNormalIndex
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagGroup
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFour

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

structure TwelveSixKCtx (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ)
    (Q H : Subgroup G) (d : ℕ) (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ) : Prop where
  ctx : TwelveCtx G M p Q H
  data : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃
  hcard : (weakBlockSet M H).ncard = 3
  h3 : CFSG.Open.pRank 3 M ≤ 3
  hm3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
    CFSG.Open.pRank 3 (CFSG.AGLEmbedding.barM M L) = 1
  hC : ∀ L W : Subgroup G, L ∈ weakBlockSet M H → Nat.card W = 3 → W ≤ L →
    Subgroup.centralizer (W : Set G) ≤ M
  hI : NineNineOneInput
  h910 : ∀ E : Subgroup G, E ≤ Q → IsElemAbelian p E → Nat.card E = p ^ 2 →
    rankThreeGamma 1 p E ≤ M → NineTenConclusion G M E H E p
  h912 : NineTwelveKerConclusion G M Q H Q p

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end

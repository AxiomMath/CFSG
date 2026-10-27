module

public import CFSG.LocalAnalysis.RankThreeUC.Section6.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section6

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

def sigmaTwoOf (G : Type) [Group G] [Finite G] (M : Subgroup G) : Set ℕ :=
  {p | p ∈ SourceSetting.sigmaOf G M ∧ CFSG.LocalAnalysis.RankThreeUC.SigmaTwo G p}

structure SigmaSylowCentralizerEscape (G : Type) [Group G] [Finite G] (M T : Subgroup G) (p : ℕ)
    (P P₀ : Subgroup G) : Prop where
  ctx : Context G M T
  prime : p.Prime
  sigma2 : p ∈ sigmaTwoOf G M
  sylow : CFSG.ABGLocalTools.IsSylowOf p P M
  le : P₀ ≤ P
  card : Nat.card P₀ = p
  notLe : ¬ Subgroup.centralizer (P₀ : Set G) ≤ M

end Section6

end CFSG.LocalAnalysis.RankThreeUC

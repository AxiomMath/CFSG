module

public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open scoped Pointwise

namespace Section11

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

structure Context (G : Type) [Group G] [Finite G] (M T : Subgroup G) : Prop where
  uc : SourceSetting.InUC G
  mSigma : SourceSetting.IsInMSigma G M
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M

@[expose] def PSet (M T : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ X ≤ M ∧ IsPGroup p X ∧ ¬ IsCyclic X ∧ (∀ x ∈ X, x ^ p = 1) ∧
    (X : Set G) * (T : Set G) = (T : Set G) * (X : Set G) ∧
    rankThreeGamma 1 p X ≤ M ∧
    (CFSG.RankThree.PartOne.IsStronglyPEmbedded p M ∨
      ∃ P Y : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P M ∧ Y ≤ P ∧
        (Y.subgroupOf P).Normal ∧ ¬ IsCyclic Y ∧ rankThreeGamma 1 p Y ≤ M)}

@[expose] def ModuleChoice (M T V₀ V : Subgroup G) : Prop :=
  (V₀, V) ∈ weakModulePairs M ∨ (V ∈ weakModules M T ∧ V₀ = ⊥)

structure Setting (G : Type) [Group G] [Finite G] (M T V₀ V : Subgroup G) : Prop where
  context : Context G M T
  moduleChoice : ModuleChoice M T V₀ V
  not_TI : ¬ CFSG.CGT.Timmesfeld75.IsTI V
  not_V1 : 2 < CFSG.Assembly.pRank 2 V₀ → V₀ ∉ normalElemAbelian2One M T
  P_empty : 2 < CFSG.Assembly.pRank 2 V₀ → PSet M T = ∅

end Section11

end CFSG.LocalAnalysis.RankThreeUC

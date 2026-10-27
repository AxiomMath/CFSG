module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual7
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def sigmaM (G : Type) [Group G] [Finite G] (M : Subgroup G) : Set ℕ :=
  {q | q ∈ rankThreeSigmaA G ∧ 2 ≤ CFSG.Open.pRank q M}

structure S15Ctx (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop where
  standing : Standing G
  uc : rankThreeUC G
  maxLocal : rankThreeIsMaxTwoLocal M
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M
  notLe : ¬ normalizer (T : Set G) ≤ M
  gn : GNSetting ↥M (T.subgroupOf M)
  pair : IsGNPair (T.subgroupOf M) T₁ T₂
  gnParabolic : GNParabolic (T.subgroupOf M) T₁ T₂
  gnThree : GNThree (T.subgroupOf M) T₁ T₂
  gnCentre : GNCentre (T.subgroupOf M) T₁ T₂
  gnAlt7 : GNAlt7 (T.subgroupOf M) T₁ T₂
  gnAltBig : GNAltBig (T.subgroupOf M) T₁ T₂
  witness : ∀ q ∈ sigmaM G M, ∃ Q : Sylow q G, IsWitness q Q M
  strong : ∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M
  noU4 : ∀ q ∈ sigmaM G M, ¬ U4Shape q M
  rank_three : ∀ q ∈ sigmaM G M, CFSG.Open.pRank q (⊤ : Subgroup ↥M) = 3
  rank_odd : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup ↥M) ≤ 3
  rank_char : ∀ q ∈ sigmaM G M, ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T →
    (C.subgroupOf T).Characteristic → CFSG.Open.pRank q (normalizer (C : Set G)) ≤ 1
  rank_N₁ : ∀ q ∈ sigmaM G M, CFSG.Open.pRank q (normalizer (T₁ : Set ↥M)) ≤ 1
  rank_N₂ : ∀ q ∈ sigmaM G M, CFSG.Open.pRank q (normalizer (T₂ : Set ↥M)) ≤ 1
  rank_C : ∀ q ∈ sigmaM G M, CFSG.Open.pRank q (gnC (T.subgroupOf M)) ≤ 1
  nonconstr : ¬ CFSG.ABGLocalTools.IsPConstrained 3 (↥M ⧸ gnC (T.subgroupOf M))

end CFSG.LocalAnalysis.RankThreeUC.S15

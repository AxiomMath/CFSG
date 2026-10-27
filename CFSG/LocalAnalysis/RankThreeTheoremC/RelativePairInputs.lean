module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

structure MaximalRelativePair (p : ℕ) (P : Sylow p G) (M D R T : Subgroup G) : Prop where
  ext : ExtremalObstruction p P M D
  not_le_normalizer : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)
  abelian : IsMulCommutative D
  maxR : rankTwoMaximalInvariantTwoSubgroup D R
  maxT : rankTwoMaximalInvariantTwoSubgroup D T
  not_le_R : ¬ R ≤ M
  le_T : T ≤ M
  inf_ne_bot : R ⊓ T ≠ ⊥
  inf_eq : R ⊓ M = R ⊓ T
  maximal : ∀ R' T' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D R' →
    rankTwoMaximalInvariantTwoSubgroup D T' → ¬ R' ≤ M → T' ≤ M →
      Nat.card (R' ⊓ T' : Subgroup G) ≤ Nat.card (R ⊓ T : Subgroup G)
  twoLocal : IsTwoLocal (normalizer ((R ⊓ T : Subgroup G) : Set G))
  twoCore : pCoreOf 2 (normalizer ((R ⊓ T : Subgroup G) : Set G)) = R ⊓ T
  le_normalizer : D ≤ normalizer ((R ⊓ T : Subgroup G) : Set G)
  pRank_eq : CFSG.Open.pRank p (normalizer ((R ⊓ T : Subgroup G) : Set G)) = 2
  not_le : ¬ normalizer ((R ⊓ T : Subgroup G) : Set G) ≤ M
  not_constrained : ¬ HasPrimeConstraint (G := normalizer ((R ⊓ T : Subgroup G) : Set G)) p

theorem gl83RelativePairExclusion_iff :
    GL83RelativePairExclusion G ↔ ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D R T : Subgroup G),
      MaximalRelativePair p P M D R T → False :=
  ⟨fun h p hp P M D R T hd => h p hp P M D hd.ext hd.not_le_normalizer hd.abelian R T hd.maxR
      hd.maxT hd.not_le_R hd.le_T hd.inf_ne_bot hd.inf_eq hd.maximal hd.twoLocal hd.twoCore
      hd.le_normalizer hd.pRank_eq hd.not_le hd.not_constrained,
    fun h p hp P M D hext hPD hab R T hR hT hRM hTM hne heq hmax hloc hcore hDle hrank hnle
      hcon => h p hp P M D R T ⟨hext, hPD, hab, hR, hT, hRM, hTM, hne, heq, hmax, hloc, hcore,
        hDle, hrank, hnle, hcon⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

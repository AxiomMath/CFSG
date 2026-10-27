module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.HighRankPair CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

universe u

@[expose] def UnitaryInvolutoryKernelsConclusion (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, twoRank (pairPointStabilizer H beta) = 1 →
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w z → Commute w t →
          Nat.card (elementFixedSet H w) =
              Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 + 1 →
            Subgroup.centralizer ({w} : Set G) ⊓
                Subgroup.centralizer (localInvolutionPointHull z w : Set G) =
              Subgroup.zpowers w ∧
            Subgroup.centralizer ({w * z} : Set G) ⊓
                Subgroup.centralizer (localInvolutionPointHull z (w * z) : Set G) =
              Subgroup.zpowers (w * z) ∧
            CFSG.oddCore (localInvolutionPointHull z w) = ⊥ ∧
            CFSG.oddCore (localInvolutionPointHull z (w * z)) = ⊥

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex

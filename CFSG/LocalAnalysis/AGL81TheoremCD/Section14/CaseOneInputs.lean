module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Cases

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactNineFourAutM : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (F Y R : Subgroup X),
    CFSG.IsQuasisimple ↥F →
    CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p (↥F ⧸ Subgroup.center ↥F) →
    Y ≤ F → Y ≠ F →
    (∃ P : Subgroup X, CFSG.ABGLocalTools.IsSylowOf p P F ∧ ∀ U : Subgroup X, U ≤ P → U ≠ ⊥ →
        F ⊓ Subgroup.normalizer (U : Set X) ≤ Y) →
    R ≤ Subgroup.normalizer (F : Set X) → R ≤ Subgroup.normalizer (Y : Set X) →
    R ⊓ Subgroup.centralizer (F : Set X) = ⊥ → (∀ x ∈ R, x ^ 3 = 1) → 9 ≤ Nat.card R →
      Nat.card R = 9 ∧ ∃ r ∈ R, r ≠ 1 ∧ ¬ F ⊓ Subgroup.centralizer ({r} : Set X) ≤ Y

@[expose] def FourteenFourOneCaseOneAt (M : Subgroup G) : Prop :=
  ∀ H E Q J : Subgroup G, S14Choice G M H E Q J → TypeA M H →
    ∀ r ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded r M

@[expose] def FourteenFourOneCaseOneGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G), FourteenFourOneCaseOneAt M

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

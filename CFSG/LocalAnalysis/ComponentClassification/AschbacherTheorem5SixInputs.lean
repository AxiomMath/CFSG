module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.Open.AschbacherComponentTypeTheorem5MilestoneDefs

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5

open CFSG.ComponentClassification.AschbacherTightEmbedding

structure SectionSixInputs : Prop where
  theorem_2_part_two : ∀ {G : Type} [Group G] [Finite G] (Q : Subgroup G),
    TightlyEmbedded Q → OddNormalizerOverlaps Q →
    Q.Normal ∨ CFSG.Open.fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (Subgroup.normalClosure (Q : Set G)))
  strongly_embedded_solvable : ∀ (K : Type) [Group K] [Finite K] (M : Subgroup K),
    CFSG.Open.fusionStronglyEmbedded M → 2 ≤ CFSG.Open.twoRank K → Group.IsSolvable M
  lemma_3_8 : ∀ {G : Type} [Group G] [Finite G] (A U : Subgroup G),
    CFSG.Open.aschbacherThm5IsSemisimple A → U ≤ Subgroup.normalizer (A : Set G) →
    AschbacherKnownGroup.IsFourGroup U →
    CFSG.Open.pRank 2 (AschbacherKnownGroup.centralizerJoin U A) ≤ 1 →
    CFSG.Open.pRank 2 A = 1
  lemma_4_9 : AschbacherTheorem3.Lemma49Statement
  knownGroups : AschbacherKnownGroup.AschbacherKnownGroupFacts

end CFSG.ComponentClassification.AschbacherTheorem5

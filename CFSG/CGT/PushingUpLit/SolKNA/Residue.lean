module

public import CFSG.CGT.PushingUpLit.SolKAb.Residue
public import CFSG.CGT.PushingUpLit.SolKAb.Vocab
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup CFSG.Assembly.LowTwoRank
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome sylowImg IsCommSubgroup)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)

@[expose] def SolomonTimmesfeldMainQuaternion : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) →
    ∀ K : Subgroup G, TightlyEmbedded K →
      IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) →
      Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set G)) →
      ∀ R : Sylow 2 K, IsQuaternionTwoGroup (sylowImg R) → MTOutcome G K R

@[expose] def SolomonTimmesfeldMainRankGe2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) →
    ∀ K : Subgroup G, TightlyEmbedded K →
      IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) →
      Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set G)) →
      ∀ R : Sylow 2 K,
        ¬ IsCommSubgroup (sylowImg R) → 2 ≤ CFSG.Open.pRank 2 (sylowImg R) →
        MTOutcome G K R

end CFSG.CGT.PushingUpLit.SolKNA

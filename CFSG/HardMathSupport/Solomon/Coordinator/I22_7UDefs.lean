module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

@[expose] def I22_7UQ : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (P U : Subgroup K), IsPGroup 3 P → U ≤ P →
    (U.subgroupOf P).Normal → 3 ≤ CFSG.Open.pRank 3 U →
      ∃ Q : Subgroup K, Q ≤ U ∧ (Q.subgroupOf P).Normal ∧ 2 ≤ CFSG.Open.pRank 3 Q ∧
        ∃ E : Subgroup K, E ≤ U ∧ IsElemAbelian 3 E ∧ Q ≤ E ∧ 3 ≤ CFSG.Open.pRank 3 E

end CFSG.HardMathSupport.Solomon.Coordinator

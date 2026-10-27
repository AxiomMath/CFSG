module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Three
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureAssembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockPLElem : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    pCoreOf 2 M ≤ S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeConclusion M S L → BlockPLThreeSolv M S L → Open.pRank 3 M ≤ 3 →
    ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      T ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → IsPGroup 3 T → IsElemAbelian 3 T

@[expose] def KFactSylowThreeAbelian : Prop :=
  (∀ d : TauCeti.ValidLieTypeIndex, IsL34Index d →
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (R : Sylow 3 X), K.Normal →
      Subgroup.centralizer (K : Set X) = ⊥ →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      (∀ x ∈ (R : Subgroup X), ∀ y ∈ (R : Subgroup X), x * y = y * x) →
      (∃ E : Subgroup X, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) →
      IsElemAbelian 3 (R : Subgroup X) ∧ Nat.card (R : Subgroup X) = 9) ∧
  (∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (R : Sylow 3 X), K.Normal →
      Subgroup.centralizer (K : Set X) = ⊥ → Nonempty (K ≃* PSL2GF 2 3) →
      (∀ x ∈ (R : Subgroup X), ∀ y ∈ (R : Subgroup X), x * y = y * x) →
      (∃ E : Subgroup X, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) →
      IsElemAbelian 3 (R : Subgroup X) ∧ Nat.card (R : Subgroup X) = 9)

end CFSG.LocalAnalysis.RankThreeTheoremC

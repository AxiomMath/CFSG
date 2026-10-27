module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

@[expose] def KFactBlockSylowThreeAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), BlockL28Hyps M S L →
    pCoreOf 2 M ≤ S → (NineThreeTwo M S L ∨ NineThreeThree M S L ∨ NineThreeFive M L) →
    Group.IsSolvable ↥(Subgroup.normalizer (S : Set G) ⊓ L) →
    ¬ 3 ∣ ((Subgroup.normalizer (S : Set G) ⊓ L).subgroupOf L).index →
    ¬ 27 ∣ Nat.card (MulAut ↥(barM M L))

end CFSG.LocalAnalysis.RankThreeTheoremC

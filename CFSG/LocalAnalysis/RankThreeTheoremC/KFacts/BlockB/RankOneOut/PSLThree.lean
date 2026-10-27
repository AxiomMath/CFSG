module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.RankOneOut.Groups
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockFiveLie
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycG2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeFive

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB

open CFSG.AGLEmbedding CFSG.AGLEmbedding.BlockCyc


theorem exists_psl_three_of_not_hasE9 {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    (hK : CFSG.Open.IsKGroup ↥M) (hA : CFSG.AGLEmbedding.Asc81bHyp M S)
    (hL : CFSG.AGLEmbedding.IsWeakSBlock M S L) (hX : ¬ CFSG.AGLEmbedding.InClassXBlock L)
    (hS : ¬ CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L)
    (hno : ¬ CFSG.AGLEmbedding.BlockCyc.HasE9 ↥(CFSG.AGLEmbedding.barM M L)) :
    ∃ f : ℕ, Odd f ∧ CFSG.Open.StatedClassicalModel
      (↥(CFSG.AGLEmbedding.barM M L) ⧸ Subgroup.center ↥(CFSG.AGLEmbedding.barM M L))
      .PSL 3 2 f := by
  rcases asc81bNineThree_holds G M S L hK hA hL with h1 | h2 | h3' | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · obtain ⟨hcl, T, J, hT, hle, hne, htop, -⟩ := nineThreeTwo_parabolic hA hL hS h2
    rcases lieFiveParabolic_of lieCyclicG2 _ hcl T J hT hle hne htop with
      hE | ⟨f, hf, hm⟩ | hA5
    · exact absurd (hasE9_of_surjective (QuotientGroup.mk'_surjective _) hE) hno
    · exact ⟨f, hf, hm⟩
    · obtain ⟨e⟩ := hA5
      exact (RankOneOut.false_of_alternating_five_parabolic e T J hT hle hne htop).elim
  · rcases lieFiveOrthogonal _ h3'.2.1 with hE | hA5
    · exact absurd hE hno
    · exact absurd
        (CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.kFactNineThreeThreeFive_proved
          G M S L hL h3' hA5) hX
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inl h4)) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inl h5))) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inl h6)))) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inr (Or.inl h7))))) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inr (Or.inr h8))))) hno

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB

end

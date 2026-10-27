module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenThreeCfgGenOf
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.RankOneOut.Groups
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeFive

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace TenOneNoAFive

theorem not_hasE9_of_alt_five {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* alternatingGroup (Fin 5)) : ¬ CFSG.AGLEmbedding.BlockCyc.HasE9 Y := by
  rintro ⟨E, -, hE⟩
  have h := Subgroup.card_subgroup_dvd_card E
  rw [hE, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h
  norm_num [Nat.factorial] at h

end TenOneNoAFive


theorem agl81TenOneNoAFiveCfg_of (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : NoXBlockFor G) (h98 : AGL81NineEightFour G) : AGL81TenOneNoAFiveCfg G := by
  intro hS p P M H Q K hd L hL
  refine ⟨fun e => ?_⟩
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hX : ¬ InClassXBlock L := (hT.nineThree_not_one hK h85 hNX hL).1
  have hSy := hT.not_isSylowTwoOf_inf hK h85 hNX hL
  rcases hT.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact hX h1
  · obtain ⟨-, T, J, hT2, hle, hne, htop, -⟩ := BlockCyc.nineThreeTwo_parabolic hA hL hSy h2
    have hcen := CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating
      (by norm_num : 4 ≤ 5) e
    exact BlockB.RankOneOut.false_of_alternating_five_parabolic
      (((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans e)
      T J hT2 hle hne htop
  · exact hX (CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.kFactNineThreeThreeFive_proved
      G M (pCoreOf 2 H) L hL h3 ⟨e⟩)
  · exact TenOneNoAFive.not_hasE9_of_alt_five e (BlockCyc.hasE9_of_nineThree_alt hL (Or.inl h4))
  · exact TenOneNoAFive.not_hasE9_of_alt_five e
      (BlockCyc.hasE9_of_nineThree_alt hL (Or.inr (Or.inl h5)))
  · exact TenOneNoAFive.not_hasE9_of_alt_five e
      (BlockCyc.hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inl h6))))
  · exact TenOneNoAFive.not_hasE9_of_alt_five e
      (BlockCyc.hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inr (Or.inl h7)))))
  · exact TenOneNoAFive.not_hasE9_of_alt_five e
      (BlockCyc.hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inr (Or.inr h8)))))

end CFSG.LocalAnalysis.RankThreeTheoremC

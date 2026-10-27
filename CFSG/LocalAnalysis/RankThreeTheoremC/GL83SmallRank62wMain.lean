module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDerive
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wNice
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zGlue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem lemma630_of_core (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactRankTwoUniqueness)
    (hK2 : KFactRankThreeStructure) (hK629 : KFactZAction629) (hI : GL83SmallRankInterface G)
    (hC : GL83SmallRankLemma630Core G) : GL83SmallRankLemma630 G := by
  intro p P M x z T hf hcov h28 f hfp hf2 hfD h29
  have hyp : Lemma630Hyp G p P M x z T f := ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩
  obtain ⟨E, hE⟩ := hC.exists_sylow p P M x z T f hyp
  have hEM : E ⊓ M = ⊥ := by
    by_cases hn : SmallRankNice p P M
    · exact sr62w_evasion_of_nice hS hU0 hK1 hK2 hyp hn hE
    · exact hC.evasion p P M x z T f hyp hn E hE
  exact lemma630_concl_of_core hS hK629 (hI.prop614 p P M x z T hf) hyp hE hEM
    (hC.iii p P M x z T f hyp)

theorem prop627W_of_coreW (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKab : KFactAbelianSylowRankThree) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hInn : KFactInnerAction) (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (hI : GL83SmallRankInterfaceW G) (hK628 : KFactZAction628) (hK629 : KFactZAction629)
    (h622 : GL83SmallRankProp622 G) (hC : GL83SmallRankLemma630Core G) :
    GL83SmallRankProp627W G :=
  prop627W_of_core hS hU0 hKab hSch hInn (hI.toInterface hS hU0 hK1 hK2) hK628 hK629 h622
    (lemma630_of_core hS hU0 hK1 hK2 hK629 (hI.toInterface hS hU0 hK1 hK2) hC)

end CFSG.LocalAnalysis.RankThreeTheoremC

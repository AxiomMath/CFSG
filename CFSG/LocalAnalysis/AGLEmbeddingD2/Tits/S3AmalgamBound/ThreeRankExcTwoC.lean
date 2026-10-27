module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankTits

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank


open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.LieType.SeitzGeneration
open scoped commutatorElement

set_option linter.unusedSectionVars false



theorem two_le_pRank_three_exc_tits {S : Type} [Group S] [Finite S]
    (hv : (LieTypeIndex.tits).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hmod := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩
  obtain ⟨K, _, _, _, hK, ⟨φ⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hmod
  obtain ⟨x, y, h, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.Tits_sylow3_cubic_witness hK
  have := two_le_pRank_three_of_extraspecial hx hz hzx hzy
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega


end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharCyc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharU42
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Tits
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbeddingD2

section


theorem offCharGen_of_seitz (hS : KFactSeitzRankTwo) : OffCharGen := by
  intro K _ _ hs hnab d ⟨e⟩ p hp hp2 hpd T hT hL34 hTits
  by_cases hex : IsD2SeitzException p d.1
  swap
  · exact glbCore_eq_top_of_seitz hS hs hnab d e hp hp2 hpd hex T hT
  obtain ⟨d, hv⟩ := d
  change IsD2SeitzException p d at hex
  rcases hex with ⟨rfl, hcase⟩ | ⟨rfl, hcase⟩
  · rcases hcase with ⟨q, hq2, hqe, hd⟩ | ⟨q, hq2, hqe, hd⟩ | ⟨q, hq2, hqe, hd⟩ |
      ⟨q, hq2, hqe, hd | hd⟩ | hd
    · subst hd
      exact absurd (isCyclic_sylow_three_linTwoEight q hq2 hqe hv e T) hT
    · exact absurd ⟨rfl, q, hq2, hqe, hd⟩ hL34
    · subst hd
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      rw [hq2, hqe] at h
      exact OffCharU42.glbCore_eq_top_of_stated_u42 h T
    · subst hd
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2
        le_rfl e
      rw [hq2, hqe] at h
      exact OffCharSp.glbCore_eq_top_of_stated_sp 3 le_rfl h T
    · subst hd
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 q hv hq2
        (by norm_num) e
      rw [hq2, hqe] at h
      exact OffCharSp.glbCore_eq_top_of_stated_sp 4 (by norm_num) h T
    · subst hd
      have h2 := kFactTitsThreeCore K ⟨.tits, hv⟩ rfl ⟨e⟩ T
      exact top_le_iff.mp (h2 ▸ glbCore_anti 3 (by norm_num : 1 ≤ 2) (T : Subgroup K))
  · rcases hcase with hd | hd
    · exact absurd ⟨rfl, hd⟩ hTits
    · subst hd
      exact absurd (isCyclic_sylow_five_suzuki 2 hv e T) hT

end

end CFSG.AGLEmbedding

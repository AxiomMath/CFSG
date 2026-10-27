module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BStruct
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BTransport
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BMoved
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit
public import CFSG.LocalAnalysis.GL83PartI.I713.Final
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62Main

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.LocalCores CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

theorem kFactBetaStructure_of_partI (h64 : KFactCenterCyclicGeFive) (h610 : GL83.I_6_10_1)
    (h7131 : GL83.I_7_13_1) (hsplit : KFactSylowSplit) : KFactBetaStructure := by
  intro p X _ _ P x z hpl hcomp
  have hcfg := cfg_of_plane63 hpl
  have hprime := hpl.prime
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  obtain ⟨L, K, hL, hK, hLK⟩ := hcomp
  have hcomp' : ∃ C C' : ComponentIndex (X ⧸ D), C ≠ C' :=
    ⟨⟨L, (CFSG.isComponent_iff_open L).2 hL⟩, ⟨K, (CFSG.isComponent_iff_open K).2 hK⟩,
      fun h => hLK (congrArg Subtype.val h)⟩
  obtain ⟨-, hcyc, hZ, hcard, htrans, hzl, hC⟩ :=
    hcfg.struct h64 h610 (fun C hC => hcfg.isCyclic_inf_of_moved h64 hC) hcomp'
  refine ⟨hcard, hZ, htrans, hzl, ?_⟩
  have hR : Open.pRank p ((P : Subgroup X).map (QuotientGroup.mk' D)) ≤ p :=
    pRank_le_of_beta hprime hpl.five_le hcfg.sylow hcfg.x_mem hcfg.x_pow
      (fun E hE hEe hxE => hcfg.card_le_of_normalizes hE hEe hxE) hcfg.catalog hcard hZ htrans hcyc
      hC (fun C => hcfg.dvd_card_comp C) h7131 hsplit
  refine le_trans ?_ hR
  refine CFSG.GH74.Uniqueness.SU.SU1.pRank_le_of fun E hEP hE k hk => ?_
  have hEp : IsPGroup p E := (P.isPGroup').to_le hEP
  have hEm : IsElemAbelian p (E.map (QuotientGroup.mk' D)) := by
    haveI := hE.1
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    show (QuotientGroup.mk' D e) ^ p = 1
    rw [← map_pow, hE.2 e he, map_one]
  have hcardm : Nat.card (E.map (QuotientGroup.mk' D)) = p ^ k := by
    rw [card_map_mk_eq hprime hEp, hk]
  exact CFSG.SectionRank.le_pRank hprime.one_lt (Subgroup.map_mono hEP) hEm hcardm


theorem kFactBetaStructure_holds
    (hsplit : KFactSylowSplit) : KFactBetaStructure :=
  kFactBetaStructure_of_partI CFSG.LocalAnalysis.RankFourTheoremC.kFactCenterCyclicGeFive_holds
    GL83.I_6_10_1_proved GL83.I713.i_7_13_1_holds hsplit

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

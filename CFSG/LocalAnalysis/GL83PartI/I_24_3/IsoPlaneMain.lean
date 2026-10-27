module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.List
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.AssemblyCover
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.AssemblySmall
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.AssemblyLFour
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.SeitzCover
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.IsoPlaneE6
import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace GL83.I243

open CFSG CFSG.Open CFSG.PreuniquenessRankFour.Helpers Subgroup CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator (sporadicMultipliers_holds)

set_option linter.unusedSectionVars true

section

theorem gl83ComponentPCoreTrivial_holds :
    CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial := by
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hList : PCoverList := pCoverList_of_tables hGA
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput sporadicMultipliers_holds
  have hCover : ThreeCoverTable := threeCoverTable_holds sporadicMultipliers_holds
  intro X _ _ hX p R K hp hp2 hrank hK hKR
  by_contra hO
  have hq : Open.IsQuasisimple ↥K := hK.2.2
  have hZ : p ∣ Nat.card (Subgroup.center ↥K) :=
    dvd_card_center_of_pCore_ne_bot hp hq hO
  obtain ⟨B, hBR, hBel, hBcard⟩ := pRank_attained p hp (R : Subgroup X)
  have hBN := normalizes_of_not_le_weakCore hp hp2 R hBR hBel hBcard hrank hK hZ hKR
  obtain ⟨z, hzB, hzK, hzc, hzp⟩ :=
    exists_mem_center_of_normalizes hp hBel (sc_of_maximal hp R hBel hBcard) hBN hZ
  have hB3 : 3 ≤ Open.pRank p B := (pRank_eq_of_max hp R hBR hBel hBcard).symm ▸ hrank
  have hCB := inf_centralizer_le_zpowers hp R hKR hBR hBel hB3 hzB hzc hzp
  obtain ⟨i, ⟨e⟩⟩ := hX.isCatalogGroup_center_quotient hK
  have hcase := hList ↥K hq p hp hp2 hZ i ⟨e⟩
  have hΩ := omega_le_zpowers_of_not_le_weakCore hp R hK hKR hBR hBel hBcard hrank hBN hzB hzK hzc
    hzp hCB
  have hcfg : Cfg p R B K z :=
    ⟨hp, hp2, hK, hKR, hBR, hBel, hBcard, hrank, hBN, hzB, hzK, hzc, hzp, hCB, hΩ⟩
  rcases hcase with ⟨d, rfl, hchar, hnex, hsc⟩ | ⟨rfl, hB | ⟨hsm | hl4, h9⟩⟩
  · rcases hsc with ⟨r, q, hd, -⟩ | ⟨r, q, hd, -⟩ | ⟨hp3, ⟨q, hd⟩ | ⟨q, hd⟩⟩
    · exact hcfg.false_of_scope seitzPlanes_classical hchar hnex
        (fun _ => ⟨by rw [hd]; trivial, by rintro ⟨-, q', hq'⟩; rw [hd] at hq'; cases hq'⟩) e
    · exact hcfg.false_of_scope seitzPlanes_classical hchar hnex
        (fun _ => ⟨by rw [hd]; trivial, by rintro ⟨-, q', hq'⟩; rw [hd] at hq'; cases hq'⟩) e
    · subst hp3
      obtain ⟨d', hv⟩ := d
      simp only at hd
      subst hd
      have htc := CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess hGA ⟨.E6 q, hv⟩ ↥K
        ⟨CoverList.isQuasisimple_of_open hq, hZ, ⟨e⟩⟩
      have hq1 : q.card % 3 = 1 := by
        have h0 := CoverList.card_pos q
        have h1 : 3 ∣ q.card - 1 := htc
        omega
      exact hcfg.false_of_e6 hq1 e hZ
    · subst hp3
      obtain ⟨d', hv⟩ := d
      simp only at hd
      subst hd
      have htc := CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess hGA
        ⟨.twistedE6 q, hv⟩ ↥K ⟨CoverList.isQuasisimple_of_open hq, hZ, ⟨e⟩⟩
      have hq2 : q.card % 3 = 2 := by
        have h0 := CoverList.card_pos q
        have h1 : 3 ∣ q.card + 1 := htc
        omega
      exact hcfg.false_of_twE6 hq2 e hZ
  · exact hcfg.false_of_cover (hCover _ hB) e hO
  · obtain ⟨hOut, h9', h27'⟩ := smallThreeFacts_holds ↥K hq i hsm ⟨e⟩
    exact hcfg.false_of_small hOut h9' h27' hZ h9
  · obtain ⟨d, rfl, hd⟩ := hl4
    exact hcfg.false_of_lfour hd lFourFacts_holds e hZ h9

end

end GL83.I243

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Chev2
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Lie
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (KFact1019 KFact131 KFactParabolicGen KFact2715
  KFactSporThree exists_not_comm_of_section_bot)

theorem p622KxThree_of_cases (hL62 : P622Lemma62Three) (hexit : P622L27Exit) (h131 : KFact131)
    (hgen : KFactParabolicGen) (h2715 : KFact2715) (h1019 : KFact1019) (hS3 : KFactSporThree)
    (hKA : KFact2713Three) (hKB : KFactL3U3SL2Three) (hKC : KFactParabolicSectionThree)
    (hKD : KFactJ1ClosureThree) (hKE : KFactThreeRankTwo) : P622KxThree := by
  intro G _ _ hS hD1 hD2 hU0 P M x z T S hf h614 hmax hle hbot L hLs hLC hzL hrk hLM hN
  have hc : P622Conf 3 P M x z T S := ⟨hf, h614, hmax, hle⟩
  have c : P622KxCfg 3 P M x z T S L := ⟨hS, hD1, hD2, hU0, hc, hLs, hLC, hzL, hrk, hLM, hN⟩
  by_cases hspor : ∃ s : TauCeti.SporadicName,
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)
  · obtain ⟨s, e⟩ := hspor
    exact c.false_of_sporadic_three hS3 hKD e
  by_cases hC2 : IsChevSimple 2 ↥L
  · exact c.false_of_chev2_three hL62 hexit h131 hgen h2715 hKC hbot hC2
  obtain ⟨i, ⟨e⟩⟩ := c.isCatalogGroup
  cases i with
  | cyclic q hq =>
    obtain ⟨a, b, hab⟩ := exists_not_comm_of_section_bot c.simple
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    have h7 : 7 ≤ n := by
      by_contra hlt
      apply hC2
      right
      refine ⟨TauCeti.CFSGIndex.alternating n hn, ?_, ⟨e⟩⟩
      show (n = 5 ∧ (2 = 2 ∨ 2 = 5)) ∨ (n = 6 ∧ (2 = 2 ∨ 2 = 3)) ∨ (n = 8 ∧ 2 = 2)
      have : 5 ≤ n := hn
      omega
    exact c.false_of_alt_three h7 ⟨e⟩
  | lie d =>
    have hd2 : d.1.characteristic ≠ 2 := by
      intro h2
      apply hC2
      left
      refine ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨e⟩⟩
      exact h2
    exact c.false_of_lieOdd_three hL62 hexit h1019 hKA hKB hKE hbot d hd2 ⟨e⟩
  | sporadic s => exact hspor ⟨s, ⟨e⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

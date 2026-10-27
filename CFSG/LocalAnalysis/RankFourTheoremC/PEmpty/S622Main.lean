module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622P65
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Even
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Odd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankD)

theorem stepL622_of_inputs (hD : S622KFactD) (hSimple : S622KFactSimple) (hP65 : S622Prop65)
    (hKx : S622Kx) : StepL622 := by
  intro G _ _ p P M x z hS hx hz h614 T hT
  by_contra hnc
  have hcfg : S62Config p P M x z T := ⟨hS, hx, hz, h614, hT⟩
  obtain ⟨S, hSconf⟩ := exists_s622Conf hcfg
  have hodd := s622_odd_core hD hSconf hnc
  have hbot := s622_primeCore_eq_bot hSimple hP65 hSconf hnc hodd
  have hnc1 : ¬ (centralizer ({x} : Set G) ≤
      (M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x) := by
    rw [hbot, sup_bot_eq]
    exact fun h => hx.not_le (h.trans inf_le_left)
  obtain ⟨L, hL, hLH, hzL, hrk, hLM, hLN⟩ := s622_apply_simple hSimple hcfg hodd hnc1
  rw [hbot] at hL hLM
  exact hKx G p P M x z hS hx hz h614 T hT hbot L hL hLH hzL hrk
    (fun h => hLM (by rw [sup_bot_eq]; exact le_inf h le_rfl)) hLN

theorem stepL622_of_kfacts (hD : S622KFactD) (hSimple : S622KFactSimple)
    (hSingle : S622KFactP65Single) (hMulti : KFactP65Multi) (hRank3 : KFactP65RankThree)
    (hRank2 : KFactP65RankTwo) (hRank4 : S622KFactP65Rank4) (hKx : S622Kx) : StepL622 :=
  stepL622_of_inputs hD hSimple (s622Prop65_of_kfacts hSingle hMulti hRank3 hRank2 hRank4) hKx

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

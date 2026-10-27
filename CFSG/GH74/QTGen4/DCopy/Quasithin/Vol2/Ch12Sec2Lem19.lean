module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem19
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem19Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

open Lem19S

theorem lem12219Solvable_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h1216 : Stmt12_2_16_F4) (h12218 : Stmt12_2_18_F4) (h1227 : Stmt12_2_7_F4) : Lem12219Solvable_F4 := by
  intro G _ _ T L V hH hNE
  obtain ⟨-, -, ⟨H, hHs⟩, -, -⟩ :=
    (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
  rw [hH.conjClosure_eq] at hHs
  by_cases hsolv : Group.IsSolvable ↥H
  · exact ⟨H, hHs, hsolv⟩
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hredV, -⟩, -, -, -, -⟩ := hall V hH.irrPlus

  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    have hne := Lem7.omegaOneCenter_inf_ne_bot hH.sylow.1 hVT hTV hH.irrPlus.2.1
      fun v hv => (S125.isElemAbelian_of_hyp1223 hH).2 v hv
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    refine (Subgroup.centralizer_le ?_).trans (hNE z hz.2 fun h => hz1 (Subtype.ext h))
    rw [Set.singleton_subset_iff]
    exact hz.1
  obtain ⟨⟨-, hCT, hO2, hker⟩, h2⟩ := h1227 G T L V H hH hCZ hHs
  obtain ⟨hLie, Y, hKY, hYmax, -, hcase⟩ := h2 hsolv
  rcases hcase with ⟨-, hA5⟩ | ⟨hA7, -, hTY, -⟩
  · exact (false_of_A5Sum hH hHs hTV (Lem18.not_card_le_four hH hredV) (h1216 G T L V hH hNE)
      (h12218 G T L V hH hNE H hHs) hCT hO2 hker (Lem7.not_le_centralizer_VZ hCZ hHs) hLie
      hA5).elim
  · exact exists_solvable_of_A7 hH hHs hKY hYmax hA7 hTY

end CFSG.Quasithin.H13

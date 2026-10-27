module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem19Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2ChainStmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Lem20
open scoped IsMulCommutative

theorem stmt12_2_20_of_solv_F4 (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (hsol : Lem12219Solvable_F4) (hpick : Lem12220Pick_F4) (htr : Lem12220Transv_F4) :
    Stmt12_2_20_F4 := by
  intro G _ _ T L V hH hNE
  obtain ⟨H, hHs, hsolv⟩ := hsol G T L V hH hNE
  obtain ⟨h, -, -, hidx, hcomm, htv⟩ := hpick G T L V H hH hNE hHs hsolv
  have hVM := normalizer_le_of_hyp1223_F4 (stmt12_2_6_of_F4 h1222 h323) hH
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hV2 : IsPGroup 2 ↥V := hH.sylow.1.to_le hVT
  have hA4 := four_le_card_of_index_eq_two
    (A := (pCoreOf 2 (V ⊔ CFSG.conjugate V h) ⊓ V).subgroupOf V) hV2
    (Lem18.not_card_le_four hH hred) hidx
  have hle : transvAxis ((pCoreOf 2 (V ⊔ CFSG.conjugate V h) ⊓ V).subgroupOf V) ≤
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V := by
    rw [← htv]
    exact autOn_le_autOn_inf hVM
  obtain ⟨n, hn, hV, hLV, hnat, hT⟩ := htr G T L V hH hcomm _ hidx hA4 hle
  exact ⟨n, hn, hV, hLV, ⟨hcomm, hnat⟩, hT⟩

theorem stmt12_2_24_config_of_solv_F4 (hsol : Lem12219Solvable_F4) (h1220 : Stmt12_2_20_F4)
    (h2123 : Lem12221_23_F4) (h24 : Lem12224Block_F4) : Stmt12_2_24_config_F4 := by
  intro G _ _ T L V hH hNE
  obtain ⟨H, hHs, hsolv⟩ := hsol G T L V hH hNE
  obtain ⟨n, hn, hV, hLV, hnat, hT⟩ := h1220 G T L V hH hNE
  obtain ⟨P, U, I, h, p, hC⟩ := h2123 G T L V H hH hNE hHs hsolv n hn hV hLV hnat hT
  have hB := h24 G T L V H P U I h n p hH hNE hC
  obtain ⟨hHs', hsolv', hn', hV', hT', -, -, hp, hp2, hP, hord, hhH, hhM, hI, hU, hUd, hUi, hUe,
    hD, hUP, hidx, htv, hUO, hUV, hK, hHU, hHI, hIP, hHIT, hIM, hQU⟩ := hC
  exact ⟨H, P, U, I, h, n, p, hHs', hsolv', hn', hV', hT', hB, hp, hp2, hP, hord, hhH, hhM, hI,
    hU, hUd, hUi, hUe, hD, hUP, hidx, htv, hUO, hUV, hK, hHU, hHI, hIP, hHIT, hIM, hQU⟩

end CFSG.Quasithin.H13

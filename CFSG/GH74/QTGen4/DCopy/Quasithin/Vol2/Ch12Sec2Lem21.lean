module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem21
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem21Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

open Lem21

theorem lem12220Pick_of_full_F4 (hpick : Lem12220PickFull_F4) : Lem12220Pick_F4 := by
  intro G _ _ T L V H hyp hNE hH hsol
  obtain ⟨P, U, I, h, p, hpre⟩ := hpick G T L V H hyp hNE hH hsol
  obtain ⟨-, -, -, -, -, hPH, -, -, -, hhP, hhM, rfl, rfl, -, -, -, -, -, hidx, hcomm, htr⟩ :=
    hpre
  exact ⟨h, hPH hhP, hhM, hidx, hcomm, htr⟩

theorem lem12221_23_of_F4 (hpick : Lem12220PickFull_F4) (h21 : Lem12221_F4) (h22 : Lem12222_F4)
    (h23 : Lem12223_F4) (hpost : Lem12223Post_F4) : Lem12221_23_F4 := by
  intro G _ _ T L V H hyp hNE hH hsol n hn hV hLV hnat hTL
  have hC : Concl12_2_20 T L V n := ⟨hn, hV, hLV, hnat, hTL⟩
  obtain ⟨P₀, U₀, I₀, h₀, p, hpre₀⟩ := hpick G T L V H hyp hNE hH hsol
  have hU₀ := h21 G T L V H P₀ U₀ I₀ h₀ n p hyp hNE hC hpre₀
  obtain ⟨P, U, I, W, h, v, hpre, hU, hdata⟩ :=
    h22 G T L V H P₀ U₀ I₀ h₀ n p hyp hNE hC hpre₀ hU₀
  have hcard := h23 G T L V H P U I W h v n p hyp hNE hC hpre hU hdata
  have hVO := not_le_pCoreOf_of_pre hpre
  obtain ⟨hUW, hHU, hHI, hIPUV, hHIT, hUCP, hQU⟩ :=
    hpost G T L V H P U I W h v n p hyp hNE hC hpre hU hdata hcard
  obtain ⟨hH', hsol', hp, hp2, -, hPH, -, -, -, hhP, hhM, hI, hUI, hUs, hUd, hUe, -, hq, hidx,
    hcomm, htr⟩ := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, hO2, -, -⟩ := hdata
  have h1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hPz, hord⟩ := eq_zpowers_of_card_eq_prime hp hcard hhP h1

  have hUV : U ⊓ V = pCoreOf 2 H ⊓ V :=
    ((eq_or_le_of_relIndex_eq_two (inf_le_inf_right V hU) inf_le_right hidx).resolve_right
      fun hle => hVO (hle.trans inf_le_left)).symm

  have hIM : ¬ I ≤ Subgroup.normalizer (L : Set G) := fun hIM =>
    hhM (hIM (hIPUV ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_left hhP)))
  refine ⟨P, U, I, h, p, hH', hsol', hn, hV, hTL, hLV, hnat, hp, hp2, hPz, hord, hPH hhP, hhM, hI,
    hUI, hUs, hUd, hUe, hq, hUCP, hidx, ⟨hcomm, htr⟩, hU, hUV, ?_, hHU, hHI, hIPUV, hHIT, hIM,
    hQU⟩
  rw [hO2, hUW]

end CFSG.Quasithin.H13

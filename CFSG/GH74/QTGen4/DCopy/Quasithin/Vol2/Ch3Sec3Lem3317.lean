module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3317A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317

public section
namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem stmt3_3_17_of_F4
    (h6 : Stmt3_3_6) (h8 : Stmt3_3_8) (h10 : Stmt3_3_10)
    (h12 : Step3_3_12R_F4) (h14 : Stmt3_3_14_F4) : Stmt3_3_17_F4 := by
  intro G _ _ T M L D h ⟨e⟩
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨_, hc⟩ := L3317.alt7_cases_F4 h8 h10 h14 h e
  rcases hc with hnat | hc4
  · exact L3317.card_commV_of_natural hnat (L3317.commV_le_vPlus h)
  · exfalso
    obtain ⟨e', hQ⟩ := L3317.exists_equiv_map_le_stabFS h e hTL
    obtain ⟨hM₁, ht₁, hn₁, hO₁, -⟩ := L3317.mOne_facts (D := D) h e' hML hTL hc4
    obtain ⟨hM₂, ht₂, hO₂, hinn₂, -⟩ := L3317.mTwo_facts h10 h e' hQ hML hTL hc4
    obtain ⟨Y, hY, -, hPSL, hInn, -⟩ := step3_3_15R_of_F4 h6 h14 h12 G T M L D (L3317.mOne L T)
      _ h hM₁ hM₂ (L3317.sup_eq_mOne_mTwo h10 h e' hQ hML hTL hc4) hO₁ hO₂ ht₁ ht₂
    rcases hY with rfl | rfl
    · exact hn₁ hPSL
    · exact hinn₂ hInn

end CFSG.Quasithin.H13

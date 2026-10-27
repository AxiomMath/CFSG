module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VBarLayer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem lemma25_input11_2_2_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) : Lemma25Ns.Input11_2_2 := by
  intro G _ _ m p hS X B L hB hBX hr hL b hb hbn
  have hnL : ¬ B ≤ Subgroup.normalizer (L : Set G) := fun h => hbn (h hb)
  obtain ⟨hp, hp2, -, hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ := i112v_bar hS hB hBX hr hL hnL
  obtain ⟨h3, -⟩ := i112v_core T TL TT TM hQK hp hp2 hQcore hBel hrankQ hLbar hnLQ
  subst h3
  obtain ⟨-, ⟨e₂⟩⟩ := i112v_layer_G T TL TT TM hS hB hBX hr hL hnL hb hbn
  have e : barOf 3 L ≃* ↥(barX 3 X L) := quotEquivBarX hp hL.1 hL.2.1
  exact ⟨e₂.trans (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm))⟩

theorem lemma27_input11_2Two_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) : Lemma27Ns.Input11_2Two := by
  intro G _ _ m hS X B L hB hBX hr hL _ b₁ hb₁ hb₁n
  exact lemma25_input11_2_2_of_tables T TL TT TM G m 3 hS X B L hB hBX hr hL b₁ hb₁ hb₁n

end CFSG.HardMathSupport.Solomon.Coordinator

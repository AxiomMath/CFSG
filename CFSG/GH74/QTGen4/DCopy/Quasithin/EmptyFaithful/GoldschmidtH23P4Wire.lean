module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Wire
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23Wire
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem lemma15123Standalone_of_fiveV_F4 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hNoE9 : SixFiveNoE9_F4) (h15 : StageLemma1515CE) (h19s : StageLemma1519)
    (h113 : StageLemma15113) (h14 : StageLemma15114) (hI20 : Lemma15120InputU_F4)
    (hI21 : Lemma15121InputU_F4) (hFive : Lemma15123FiveInputV) : Lemma15123Standalone_F4 := by
  have h1416 : StageLemma1416 := stageLemma1416_of_a3 h37 h38 h39
  intro G _ _ T Mc M hq hM hCE h5
  obtain ⟨Z₁, Z₂, V₁, V₂, hSX, hY⟩ := exists_setting_six5_with_YV hq hM h5 (h15 G T Mc M hq hM hCE)
    (h19s G T Mc M hq hM hCE) (h113 G T Mc M hq hM hCE).four (hNoE9 G T Mc M hq hM hCE h5)
  have hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂ := hSX.toSetting1516
  have hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ := ⟨hq, hM, hCE, hS⟩
  have h15' := h15 G T Mc M hq hM hCE
  have h14' := h14 G T Mc M hq hM hCE
  have h19' := h19s G T Mc M hq hM hCE
  have h17 := lemma_15_1_17 hq hM hS h19'
  have h18c := lemma_15_1_18 as116Statement hC hSX.toExtra h15' h14' h19' h17
  have hx18 := lemma_15_1_18_extra hC hSX.toExtra h15' h14' h19' h17
  have h19c := lemma_15_1_19_used h37 h38 hC h18c hx18
  obtain ⟨L, hLc, hLq, hLn⟩ := h19c.six
  have hL : IsL1519 Mc Z₁ L := ⟨hLc, hLq, hLn⟩
  have hL20 : IsL1520 T Mc Z₁ L := hL.isL1520 h18c.four (hS.pCore_g1_ne_bot hq hM)
  have h20 : Lemma15120Concl T Mc M Z₁ L := by
    obtain ⟨h2, h3⟩ := hI20 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL hx18
    exact ⟨lemma_15_1_20_sylow h18c.four hL20,
      lemma_15_1_20_one (h1416 G T Mc hq).1 hM h15' hL20, h2,
      fun hc => ⟨isPGroup_two_center_of_isComponentOf1515c hc h19c.one, h3 hc⟩⟩
  have h21 : Lemma15121Concl Mc Z₁ L := hI21 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hx18
  exact hFive G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h20 h21 h5 hSX.toExtra hY

end CFSG.Quasithin

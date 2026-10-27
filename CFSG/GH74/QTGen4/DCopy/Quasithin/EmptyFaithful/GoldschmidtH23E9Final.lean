module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23E9LemEDef
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23E9Types
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23Wire

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem sixFiveNoE9_of_inputs_F4 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h116 : AS116Statement) (h15 : StageLemma1515CE) (h19s : StageLemma1519)
    (h113 : StageLemma15113) (h14 : StageLemma15114) (hT : Lemma15120TypesInput_F4)
    (hLE : Lemma15121E9_F4) (hFive : Lemma15123FiveInputC) : SixFiveNoE9_F4 := by
  intro G _ _ T Mc M hq hM hCE h5 hE9
  have h15' := h15 G T Mc M hq hM hCE
  have h14' := h14 G T Mc M hq hM hCE
  have h19' := h19s G T Mc M hq hM hCE
  have h113' := (h113 G T Mc M hq hM hCE).four
  obtain ⟨Z₁, Z₂, V₁, V₂, hE, -⟩ :=
    exists_e9Ctx hq hM hCE h5 hE9 h15' h19' h14' h113'
  have hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ := hE.ctx
  have h17 := lemma_15_1_17 hq hM hC.setting h19'
  obtain ⟨-, hMc⟩ := vZ_mc_eq_vE hq hM hCE h5 hE9 h15' h19' h14' h113'
  obtain ⟨hQ1, hQn⟩ := q1_normal hq hM hCE hE.pre h15' h19' h14' h113'
  have hQ : T ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) := hq.t_le_mc.trans hQn
  have h18 := lemma_15_1_18_of_q3 h116 hC h14' h17 hQ
  have h19c := lemma_15_1_19_used_e9 h37 h38 hC h18 h14' hMc hQ1
  obtain ⟨L, hLc, hLq, hLn⟩ := h19c.six
  have hL : IsL1519 Mc Z₁ L := ⟨hLc, hLq, hLn⟩
  obtain ⟨Y', hY1, hY2, hY3, hY4, hY5, hY6, hY7, hY8⟩ := hE.y5
  exact hFive G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19c hL
    (hT G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19c hL)
    (hLE G T Mc M Z₁ Z₂ V₁ V₂ L hE h17 h18 h19c hL) h5
    ⟨Y', hY1, hY2, hY3, hY4, hY5, hY6, hY7, hY8,
      factor_of_e9 hq hM hCE hE.pre h15' h19' h14' h113' hY1 hY3 hY5⟩

end CFSG.Quasithin.E9

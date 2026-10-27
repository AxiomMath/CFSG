module

public import CFSG.Quasithin.EmptyFaithful.T1515cE
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1515Stage
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1515cTop

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Lemma15120InputU_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15118Extra T Mc M Z₁ →
    (CharTwo L → ⁅L, thompsonJ (s1516 T Z₁)⁆ = L ∧
      (Case15120TwoA T Mc Z₁ L ∨ Case15120TwoB T Mc Z₁ L ∨ Case15120TwoC Mc Z₁ L)) ∧
    (IsComponentOf L (g1_1516 Z₁) →
      Case15120ThreeA Mc Z₁ L ∨ Case15120ThreeB Mc Z₁ L ∨ Case15120ThreeC T Mc Z₁ L ∨
        Case15120ThreeD T Mc Z₁ L ∨ Case15120ThreeE T Mc Z₁ L)

@[expose] def Lemma15121InputU_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → Lemma15118Extra T Mc M Z₁ → Lemma15121Concl Mc Z₁ L

@[expose] def Lemma15122InputU_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15120Concl T Mc M Z₁ L →
    Lemma15121Concl Mc Z₁ L → Lemma15118Extra T Mc M Z₁ → Lemma15122Concl T Mc M Z₁ L

@[expose] def Lemma15128InputU_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L → Lemma15125Concl T Z₁ V₁ L → Lemma15126Concl L →
    Lemma15127Concl Z₂ L → Lemma15128Concl T Mc Z₁ Z₂ L

@[expose] def Lemma15129InputU_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L → Lemma15125Concl T Z₁ V₁ L → Lemma15126Concl L →
    Lemma15127Concl Z₂ L → Lemma15128Concl T Mc Z₁ Z₂ L → Lemma15129Concl Z₂ L

theorem theorem1515_of_inputs3_ce3_F4 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h15 : StageLemma1515CE) (h157 : StageLemma1517) (h19s : StageLemma1519)
    (h110 : StageLemma15110) (h113 : StageLemma15113) (h14 : StageLemma15114)
    (hD : M11TypesDisjoint1522) (h23 : Lemma15123Standalone_F4)
    (hI20 : Lemma15120InputU_F4) (hI21 : Lemma15121InputU_F4) (hI22 : Lemma15122InputU_F4)
    (hI24 : Lemma15124InputU) (hI25 : Lemma15125InputRestU) (hI27 : Lemma15127InputU)
    (hI28 : Lemma15128InputU_F4) (hI29 : Lemma15129InputU_F4) : StageTheorem1515_F4 := by
  have h1416 : StageLemma1416 := stageLemma1416_of_a3 h37 h38 h39
  intro G _ _ T Mc M hq hM hCE hce
  have hsmall : Ce15Small T Mc M :=
    ce15Small_of_not_six_five hce (h23 G T Mc M hq hM hCE)
  obtain ⟨Z₁, Z₂, V₁, V₂, hSX⟩ := exists_setting_of_ce15Small h15 h157 h19s h110 h113 hq hM hCE hsmall
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
  have h22 : Lemma15122Concl T Mc M Z₁ L :=
    hI22 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h20 h21 hx18
  have h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L := by
    obtain ⟨h1, h2⟩ := hI24 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 hsmall
    have h7 := not_seven_of_four_or_six h1
    exact ⟨h1, (hS.decomp_other h7).2.1, h2, lemma_15_1_24_three hS h15' hsmall,
      (hS.y_facts hsmall).1.2.2.1, lemma_15_1_24_four hq hM hS hsmall h1⟩
  have h25 : Lemma15125Concl T Z₁ V₁ L := by
    obtain ⟨h1, h3, h5⟩ := hI25 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 h24
    exact ⟨h1, lemma_15_1_25_two hD hC h15' h19' h19c.one h17 h22 h24 h1, h3,
      lemma_15_1_25_four hS h24.one, h5, lemma_15_1_25_six hS h24.one⟩
  have h26 := lemma_15_1_26 hL h22 h24 h25
  have h27 : Lemma15127Concl Z₂ L := hI27 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 h24 h25 h26
  have h28 : Lemma15128Concl T Mc Z₁ Z₂ L :=
    hI28 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 h24 h25 h26 h27
  have h29 : Lemma15129Concl Z₂ L :=
    hI29 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 h24 h25 h26 h27 h28
  exact h29 h28.1

end CFSG.Quasithin

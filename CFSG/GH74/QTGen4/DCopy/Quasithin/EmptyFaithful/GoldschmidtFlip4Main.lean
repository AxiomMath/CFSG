module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFlip4Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S151S0
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1515cTop

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise commutatorElement

theorem input15122ThreeEFlip4Star_holds_F4 (h23 : Lemma15123Standalone_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h36 : A36ForSQTK) (hF : A318Facts) (kN : L45NotA38Type)
    (hl42 : ∀ (X : Type) [Group X] [Finite X], IsPSL 4 2 1 X → A318Exclusion X) :
    Input15122ThreeEFlip4Star_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L P hc h3E h4 hfl hP _
  have hsmall : Ce15Small T Mc M :=
    ce15Small_of_not_six_five hc.ctx.setting.ce15
      (h23 G T Mc M hc.ctx.qtfe hc.ctx.mf hc.ctx.ce)
  exact flip4_star_all h37 h38 h36 hF kN hl42 hc hsmall h3E h4 hfl hP

end CFSG.Quasithin

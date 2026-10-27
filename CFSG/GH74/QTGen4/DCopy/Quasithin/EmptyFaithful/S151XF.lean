module

public import CFSG.Quasithin.EmptyFaithful.S151XF
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Input15120TwoB_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ListD15120 L → Case15120TwoB T Mc Z₁ L

theorem lemma15120InputU_of_named_inputs_F4 (nLJ : Input15120LJ) (nB42 : Input15120B42List)
    (nA : Input15120L2Block) (nB : Input15120RankTwoExcl) (nC : Input15120L45)
    (nD : Input15120TwoB_F4) (nCL : Input15120CompList) (mA : Input15120MLA) (mB : Input15120MLB)
    (mC : Input15120MLC) (mD : Input15120MLD) (mE : Input15120MLE) : Lemma15120InputU_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL hx
  have hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L :=
    ⟨hC, h17, h18, h19, hL.isL1520 h18.four (hC.setting.pCore_g1_ne_bot hC.qtfe hC.mf)⟩
  refine ⟨fun hchar => ⟨nLJ G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar, ?_⟩, fun hcomp => ?_⟩
  · rcases nB42 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar with h | h | h | h
    · exact Or.inl ((nA G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h).2 hL.comp)
    · exact (nB G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h).elim
    · exact Or.inr (Or.inr (nC G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h))
    · exact Or.inr (Or.inl (nD G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h))
  · rcases nCL G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hx with h | h | h | h | h
    · exact Or.inl ⟨h, mA G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h⟩
    · exact Or.inr (Or.inl ⟨h, mB G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h, mC G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, mD G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h hx⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, mE G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h⟩)))

end CFSG.Quasithin

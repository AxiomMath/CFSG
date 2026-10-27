module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Sz
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.PslTwo
public import CFSG.HardMathSupport.Dickson.Sec6.I1431

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Dickson.Sec6.I923

@[expose] def Y1431_D4 : Prop := Y1431NoCfgAt FamD4

@[expose] def Y1431_F4 : Prop := Y1431NoCfgAt FamF4

@[expose] def Y1431_E6Good : Prop := Y1431NoCfgAt FamE6Good

@[expose] def Y1431_E6Bad : Prop := Y1431NoCfgAt FamE6Bad

@[expose] def Y1431_TwE6Good : Prop := Y1431NoCfgAt FamTwE6Good

@[expose] def Y1431_TwE6Bad : Prop := Y1431NoCfgAt FamTwE6Bad

@[expose] def Y1431_E7 : Prop := Y1431NoCfgAt FamE7

@[expose] def Y1431_E8 : Prop := Y1431NoCfgAt FamE8

theorem i1431LieRest_of_families
    (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (h0 : CFSG.HardMathSupport.Solomon.Coordinator.L2CentreThree)
    (hPslGood : Y1431NoCfgAt FamPslGood) (hPslBad : Y1431NoCfgAt FamPslBad) (hPsp : Y1431NoCfgAt FamPsp)
    (hPspTwoEight : Y1431NoCfgAt FamPspTwoEight) (hPsuGood : Y1431NoCfgAt FamPsuGood)
    (hPsuBadRest : Y1431NoCfgAt FamPsuBadRest) (hU6 : Y1431LieRestAt FamU6Real) (hOrthOdd : Y1431NoCfgAt FamOrthOdd)
    (hOrthPlus : Y1431NoCfgAt FamOrthPlus) (hOrthMinus : Y1431NoCfgAt FamOrthMinus) (hD4 : Y1431_D4)
    (hTriD4 : Y1431NoCfgAt FamTriD4) (hG2 : Y1431NoCfgAt FamG2) (hF4 : Y1431_F4) (hE6Good : Y1431_E6Good)
    (hE6Bad : Y1431_E6Bad) (hTwE6Good : Y1431_TwE6Good) (hTwE6Bad : Y1431_TwE6Bad)
    (hE7 : Y1431_E7) (hE8 : Y1431_E8) (hReeG2 : Y1431NoCfgAt FamReeG2) (hReeF4 : Y1431NoCfgAt FamReeF4) :
    I1431LieRest := by
  have hPslTwo := y1431_noCfg_pslTwo CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds
    CFSG.HardMathSupport.Solomon.Coordinator.l2Aut3Classification_holds
    CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds h0
  have hSz := y1431_noCfg_sz hO
  intro Y _ _ Â ξ J q c ⟨t, n, p, f, hadm, ht, hm⟩ q0 hq0 hqq
  rcases fam1431_cover hadm ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h
  · exact (hPslTwo Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hPslGood Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hPslBad Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hPsp Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hPspTwoEight Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hPsuGood Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hPsuBadRest Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact hU6 Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq
  · exact (hOrthOdd Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hOrthPlus Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hOrthMinus Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hD4 Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hTriD4 Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hG2 Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hF4 Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hE6Good Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hE6Bad Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hTwE6Good Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hTwE6Bad Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hE7 Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hE8 Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hSz Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hReeG2 Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim
  · exact (hReeF4 Y Â ξ J q c t n p f hadm ht h hm q0 hq0 hqq).elim

end CFSG.HardMathSupport.Dickson.Sec6.I1431

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2b

public section


namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Blueprint TauCeti
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (KD264InnGood)

theorem lvCtx_holds : LvCtx where
  ord := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  tup := tupleLemma_holds
  nc2 := CFSG.LocalAnalysis.GLTheoremA.List93.notChev2_holds
  xchar := fun _ _ _ _ _ hS ho =>
    CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hS ho
  odd := fun _ _ _ _ hr hr2 hd e => CFSG.LocalAnalysis.GLTheoremA.small_odd_lie hr hr2 hd e

theorem kDescFamRes_omegaPlus_holds (p : ℕ) : KDescFamRes p fOmegaPlus :=
  kDescFamRes_omegaPlus_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds p

theorem kDescFamRes_omegaMinus_holds (p : ℕ) : KDescFamRes p fOmegaMinus :=
  kDescFamRes_omegaMinus_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds p

theorem kDescFamRes_e6_holds (p : ℕ) : KDescFamRes p fE6 :=
  kDescFamRes_e6_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds p

theorem kDescFamRes_e7_holds (p : ℕ) : KDescFamRes p fE7 :=
  kDescFamRes_e7_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds p

theorem kDescFamRes_e8_holds (p : ℕ) : KDescFamRes p fE8 :=
  kDescFamRes_e8_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds p

theorem kDescFamRes_f4_holds (p : ℕ) : KDescFamRes p fF4 :=
  kDescFamRes_f4_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds p

theorem kDescFamRes_twE6_holds (p : ℕ) : KDescFamRes p fTwE6 :=
  kDescFamRes_twE6_aux lvCtx_holds CFSG.LocalAnalysis.GLTheoremA.k3NotChev2At_holds p

end CFSG.LocalAnalysis.GLTheoremA.HDesc

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.AsmMain
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentHolds
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardMain
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardE7
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardCentre
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardOrders
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1OfCI
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.Adapters.CatalogAgree

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.HarrisLit


theorem f3HigherRankFalse_of_ci (hCI : GSLit.ClassicalInvolutionInput)
    (hLB : CFSG.Open.LBalanceStatement) : F3HigherRankFalse := by
  have hT1 : Harris82Theorem1KProper := T1.harris82Theorem1KProper_of_ci hCI
  have hGA : TBLit.GriessMultipliersAllModels := TBLit.griessMultipliersAllModels_holds
  have hGr : CFSG.Open.GriessAllModelsStatement :=
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  have hC2 : POmegaPlusCentreExpTwo := pOmegaPlusCentreExpTwo_of_griess hGr
  have hbr : Assembly.CatalogImp Blueprint.Catalog Assembly.InCatalog :=
    fun X _ _ _ _ hX => CFSG.Open.QTFaithfulEmptyTauCeti.inCatalog_of_catalog X hX
  have hFE7 : T1.P51Q.FamF .E7 := T1.P51Q.famF_E7
  have hFTE6 : T1.P51Q.FamF .twistedE6 := T1.P51Q.famF_twistedE6
  have h51 : T1.Harris82Lemma51Quat :=
    T1.P51Q.harris82Lemma51Quat_of_famF T1.P51Q.famF_psl T1.P51Q.famF_psu T1.P51Q.famF_PSp
      T1.P51Q.famF_POmegaOdd T1.P51Q.famF_POmegaPlus T1.P51Q.famF_POmegaMinus
      T1.P51Q.famF_G2 T1.P51Q.famF_F4 T1.P51Q.famF_E6 hFE7 T1.P51Q.famF_E8 hFTE6
      T1.P51Q.famF_trialityD4 T1.P51Q.famF_twistedG2
  have hKR : T1.KnownRowThree := T1.F3FG.knownRowThree_holds hCI h51
  have hHB : HardBranchInputBalanced :=
    hardBranchInput_of_balanced (hardBranchBalanced hT1 hLB hbr hKR hC2
      LinUnit.linUnitInvolutionComponents_holds (pOmegaPlusNotLinUnit_of_orders
          ComponentClassification.CatLeafProof.lieOrderFormulasInput)) hGr
  exact f3HigherRankFalse_of_inputs hT1 identGenInput_holds hHB hGA hC2
      (pOmegaPlusNotLinUnit_of_orders ComponentClassification.CatLeafProof.lieOrderFormulasInput)

end CFSG.OddStandard.HigherRank.F3

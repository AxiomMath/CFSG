module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Core
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUBlockTransfer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUOrder
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherOne
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Setup
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1FourGroup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAlt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStatements
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoreBasics
public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxDef
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSkel
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Simple
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.AllFixed
public import Certificates.Certificate7233Base

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup CFSG.ASVolI.ChIJK

theorem pslUnitU43Leaf_holds : G2Three.PSLUnitU43Leaf := by
  intro S _ _ _ n r _ _ hm t ht J hJle hsub _ hq hmodel
  have hC : IsComponentIn J (centralizer ({t} : Set S)) := ⟨hJle, hq, hsub⟩
  rcases hm with hm | hm
  · exfalso
    obtain ⟨t', k, s, hmem, hadm, hlm⟩ :=
      isComponentIn_modelIn_psl Nat.prime_three (by norm_num) hm ht hC
    obtain rfl : t' = .PSL := luLinTuples_fst hmem
    exact lieModel_psl_ne_psu43 hadm hlm hmodel
  · exact isComponentIn_hasFourElt_psu hm ht hC hmodel

end CFSG.OddStandard.HigherRank.LinUnit

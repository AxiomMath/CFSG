module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Defs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
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
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Simple
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.AllFixed
public import Certificates.Certificate7233Base

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup

theorem isSU43_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsSU43 B) :
    IsSU43 A := by
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h.1, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, h.2.1]
  · exact (MulEquiv.isCyclic (Subgroup.centerCongr e)).2 h.2.2.1
  · exact CFSG.ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv
      (CFSG.ComponentClassification.UnbalancingLocal.centerQuotientCongr e).symm h.2.2.2

theorem isSU43_quotient_oddCore_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A]
    [Finite B] (e : A ≃* B) (h : IsSU43 (B ⧸ CFSG.oddCore B)) :
    IsSU43 (A ⧸ CFSG.oddCore A) := by
  have hmap : (CFSG.oddCore A).map e.toMonoidHom = CFSG.oddCore B := by
    rw [CFSG.oddCore_eq_piCore A, CFSG.oddCore_eq_piCore B]
    exact CFSG.LocalCores.piCore_map_mulEquiv _ e
  exact isSU43_of_mulEquiv (QuotientGroup.congr _ _ e hmap) h

end CFSG.OddStandard.HigherRank.G2Three

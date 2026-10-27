module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Core
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs
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
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Simple
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.AllFixed
public import Certificates.Certificate7233Base

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.ComponentClassification.HarrisLit

theorem lieModel_quotient_center_of_isSU43 {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple K) (hB : IsSU43 (K ⧸ CFSG.oddCore K)) :
    CFSG.Blueprint.LieModel (K ⧸ center K) .PSU 4 3 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : CFSG.oddCore K = CFSG.pPrimeCore 2 K := by
    rw [CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]
  let e : K ⧸ CFSG.oddCore K ≃* K ⧸ CFSG.pPrimeCore 2 K :=
    QuotientGroup.quotientMulEquivOfEq hcore
  have hQ : CFSG.IsQuasisimple (K ⧸ CFSG.pPrimeCore 2 K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hB.1
  obtain ⟨e₁⟩ :=
    CFSG.ComponentClassification.UnbalancingLocal.nonempty_center_quotient_core hq hQ
  have hLie : CFSG.Blueprint.LieModel
      ((K ⧸ CFSG.pPrimeCore 2 K) ⧸ center (K ⧸ CFSG.pPrimeCore 2 K)) .PSU 4 3 1 :=
    CFSG.ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv
      (CFSG.ComponentClassification.UnbalancingLocal.centerQuotientCongr e) hB.2.2.2
  exact CFSG.ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv e₁.symm hLie

theorem inductionTypeField_of_isSU43 {K : Type} [Group K] [Finite K]
    (hB : IsSU43 (K ⧸ CFSG.oddCore K)) : T1.InductionTypeField 3 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : CFSG.oddCore K = CFSG.pPrimeCore 2 K := by
    rw [CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]
  let e : K ⧸ CFSG.oddCore K ≃* K ⧸ CFSG.pPrimeCore 2 K :=
    QuotientGroup.quotientMulEquivOfEq hcore
  refine ⟨1, le_refl 1, Or.inr (Or.inr (Or.inl ?_))⟩
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hB.1, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, hB.2.1]
    norm_num
  · exact CFSG.ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv
      (CFSG.ComponentClassification.UnbalancingLocal.centerQuotientCongr e) hB.2.2.2

end CFSG.OddStandard.HigherRank.G2Three

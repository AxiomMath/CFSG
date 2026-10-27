module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OddCoreBridge
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseBabySchreier
public import CFSG.Monster.B.CTIB.OddCoreFree
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import Certificates.Certificate3085Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Monster.B

theorem babyOddCore
    : BabyOddCore := by
  have hC : InvolutionOddCoreTrivial Cbar :=
    involutionOddCoreTrivial_of_oddCore fun t ht =>
      CTIB.native_B_all_involution_centralizers_odd_core_free.2.1 t ht
  obtain ⟨ι⟩ := ComponentClassification.BMCase.nonempty_pinnedB_equiv_Cbar
  exact @InvolutionOddCoreTrivial.of_mulEquiv NativeSporadic.B Cbar inferInstance _ ι hC

end CFSG.EvenSporadicStandard.Induction

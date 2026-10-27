module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovAlt
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovMathieu
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovM12
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovJ1
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovJ2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovMcL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovLy
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovL3U3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovSp4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovExc
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovPGL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovPGU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovRee
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovBender
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovL34
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abG2Native
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4Native
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3U3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3U3Small
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Model
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGU
public import CFSG.GH74.GLS.SP.Consistency
public import CFSG.GH74.GLS.SP.Generic
public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.GLS.Stage2.Final.ModelIVKGen
public import CFSG.GH74.GLS.Stage2.Final.ModelLUMain
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerBar
public import CFSG.GH74.Generic.BarSubnormal
public import CFSG.GH74.Generic.S1.DecompCore
public import CFSG.GH74.Generic.S1.KL3Red
public import CFSG.GH74.Generic.S1.TFrame
public import CFSG.GH74.Generic.S1.TLeafA
public import CFSG.GH74.Generic.S1.TLeafBar
public import CFSG.GH74.Generic.S45.LEvSporFacts
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorU
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPair
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.RankThree.PartOne.KS.Plane
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

theorem ivk93CovLeaves_proved
    : Ivk93CovLeaves := by
  exact
    { alt := ivk93cov_alt
      m11 := ivk93cov_m11
      m12 := ivk93cov_m12
      m22 := ivk93cov_m22
      m23 := ivk93cov_m23
      j1 := ivk93cov_j1
      j2 := ivk93cov_j2
      j3 := ivk93cov_j3
      mcl := ivk93cov_mcl
      ly := ivk93cov_ly
      l2 := ivk93cov_l2
      l3 := ivk93cov_l3
      u3 := ivk93cov_u3
      sp4 := ivk93cov_sp4
      g2 := ivk93cov_g2
      d4 := ivk93cov_d4
      l4 := ivk93cov_l4
      u4 := ivk93cov_u4
      l5 := ivk93cov_l5
      u5 := ivk93cov_u5
      ree := ivk93cov_ree
      l28 := ivk93cov_l28
      l216 := ivk93cov_l216
      l34 := ivk93cov_l34
      u34 := ivk93cov_u34
      sz8 := ivk93cov_sz8 }

theorem ivk93CovJ_proved
    : Ivk93CovJ :=
  ivk93CovJ_of_leaves ivk93CovLeaves_proved

theorem ivk93cov_oneClass_proved :
    Ivk93CovOneClass := by
  intro J _ _ hJ u v hu hv
  rcases hJ with hJ | hJ
  · exact ivk93cov_mcl_oneClass hJ u v hu hv
  · exact ivk93cov_ly_oneClass hJ u v hu hv

end CFSG.GH74.GLS.IVK.Proofs2

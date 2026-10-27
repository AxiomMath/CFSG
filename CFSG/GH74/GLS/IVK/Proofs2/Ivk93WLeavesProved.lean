module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93R3Main
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WSmall1
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WSmall2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WSpor
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WQuasi
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WSp4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WExc
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WL3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WL4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WL5
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WU3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WU4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WU5
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.E2.OddRankG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4U3Out
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Exc2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Defs
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Main
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
public import CFSG.RankThree.PartOne.KS.Plane
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

theorem ivk93wLeaves_proved
    : Ivk93WLeaves := by
  exact
    { alt := ivk93w_alt
      m11 := ivk93w_m11
      m12 := ivk93w_m12
      m22 := ivk93w_m22
      m23 := ivk93w_m23
      j1 := ivk93w_j1
      j2 := ivk93w_j2
      j3 := ivk93w_j3
      mcl := ivk93w_mcl
      ly := ivk93w_ly
      l2 := ivk93w_l2
      l3 := ivk93w_l3
      u3 := ivk93w_u3
      sp4 := ivk93w_sp4
      g2 := ivk93w_g2
      d4 := ivk93w_d4
      l4 := ivk93w_l4
      u4 := ivk93w_u4
      l5 := ivk93w_l5
      u5 := ivk93w_u5
      ree := ivk93w_ree
      l28 := ivk93w_l28
      l216 := ivk93w_l216
      l34 := ivk93w_l34
      u34 := ivk93w_u34
      sz8 := ivk93w_sz8 }

theorem Ivk93Adapt.ivk93_res3_proved
    : Ivk93Adapt.Ivk93G2Res3 := by
  exact Ivk93Adapt.ivk93_res3 ivk93wLeaves_proved

end CFSG.GH74.GLS.IVK.Proofs2

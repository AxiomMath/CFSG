module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Alt2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Mathieu2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M122
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93J12
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93J22
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93J32
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93McL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Ly2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L22
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGU2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Sp42
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Exc2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L42
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L52
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93U42
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93U52
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Ree2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Bender2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L342
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGU
public import CFSG.GH74.GLS.SP.Consistency
public import CFSG.GH74.GLS.SP.Generic
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

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint

theorem ivk93Leaves2_proved :
    Ivk93Leaves2 := by
  exact
    { alt := ivk93_alt2
      m11 := ivk93_m112
      m12 := ivk93_m122
      m22 := ivk93_m222
      m23 := ivk93_m232
      j1 := ivk93_j12
      j2 := ivk93_j22
      j3 := ivk93_j32
      mcl := ivk93_mcl2
      ly := ivk93_ly2
      l2 := ivk93_l22
      l3 := ivk93_l32
      u3 := ivk93_u32
      sp4 := ivk93_sp42
      g2 := ivk93_g22
      d4 := ivk93_d42
      l4 := ivk93_l42
      u4 := ivk93_u42
      l5 := ivk93_l52
      u5 := ivk93_u52
      ree := ivk93_ree2
      l28 := ivk93_l282
      l216 := ivk93_l2162
      l34 := ivk93_l342
      u34 := ivk93_u342
      sz8 := ivk93_sz82 }

theorem ivk93Pair2_proved :
    Ivk93Pair2 :=
  ivk93Pair2_of_leaves ivk93Leaves2_proved

end CFSG.GH74.GLS.IVK.Proofs2

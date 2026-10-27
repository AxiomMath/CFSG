module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29A1
public import CFSG.GH74.Generic.JMaxCongr
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

@[expose] def NoL3PumpupOfA7Step (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (b u : G) (J M : Subgroup G), PumpUpLT 2 b J u M → IsA7Bar J → b ∈ M →
    ¬ QShape3 (↥M ⧸ pPrimeCore 2 ↥M)

end CFSG.GH74.Generic.BProg.B3

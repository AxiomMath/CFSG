module

public import Certificates.Certificate129021
public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped Matrix

theorem b_heisCfg : ∃ (x y : Fin 4 → NativeSporadic.B) (z : NativeSporadic.B),
    HeisCfg 3 4 x y z ∧ ∀ i, y i ^ 3 = 1 :=
  Certificates.certificate129021

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

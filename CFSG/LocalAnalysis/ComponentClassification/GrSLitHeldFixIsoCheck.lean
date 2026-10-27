module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixGraph
public import CFSG.Sporadic.SmallOddCore.HeLocalCheck
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificate
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixGraph
public meta import CFSG.Sporadic.SmallOddCore.HeLocalCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixIsoCheckInputs
public import Certificates.Certificate2020

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore

theorem heldFix_words_lt : (∀ i < 3, ∀ j ∈ heldFixXWords.getD i [], j < 5) ∧
    ∀ j < 5, ∀ i ∈ heldFixSWords.getD j [], i < 3 := by
  decide

theorem heldFix_graph_check :
    enumOK 147 heldFixGraphGens heldFixGraphEnum = true ∧ heldFixGraphEnum.tabs.size = 20160 :=
  Certificates.certificate2020

end CFSG.ComponentClassification.GrSLit.HeldFix

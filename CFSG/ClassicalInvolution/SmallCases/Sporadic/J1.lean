module

public import CFSG.ClassicalInvolution.Generic.Generation.Endgame
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport

public section

namespace CFSG.ClassicalInvolution

theorem noNonsolvableClassical_J1 :
    NoNonsolvableClassical CFSG.Blueprint.NativeSporadic.J1 :=
  NoNonsolvableClassical.of_mulEquiv CFSG.ProperTwoGeneratedCore.j1_exact_model_equiv.symm
    noNonsolvableClassical_properTwoGenCoreJ1

end CFSG.ClassicalInvolution

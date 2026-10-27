module

public import CFSG.HardMathSupport.Malle.Coordinator.CaseTwoFinal
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4YMaximal
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4CyclicToralFinal
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4IndexSieveProof
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4InvolutionCentralizer

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

theorem reeF4CaseTwoInvariant_of_certs :
    ReeF4CaseTwoInvariant :=
  reeF4CaseTwoInvariant_of LocalAction.reeF4CyclicToralCentralizers_of_certs
    LocalAction.reeF4InvolutionCentralizerCoprime_of_certs
    LocalAction.reeF4SylowNormalizerCard_of_certs LocalAction.reeF4OuterSigmaFixedOrder_of_certs
    LocalAction.reeF4IndexSieve_proof

theorem kFactReeF4Local_of_certs :
    CFSG.AGLEmbedding.KFactReeF4Local :=
  LocalAction.kFactReeF4Local_of_caseTwoInvariant reeF4CaseTwoInvariant_of_certs

end CFSG.HardMathSupport.Malle.Coordinator

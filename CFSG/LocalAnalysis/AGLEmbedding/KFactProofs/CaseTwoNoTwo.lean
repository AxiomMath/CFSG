module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwoL28
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwoSz32

public section

namespace CFSG.AGLEmbedding

theorem kFactCaseTwoNoTwo :
    KFactCaseTwoNoTwo :=
  kFactCaseTwoNoTwo_of_halves kFactCaseTwoNoTwoL28 kFactCaseTwoNoTwoSz32

end CFSG.AGLEmbedding

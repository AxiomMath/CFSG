module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCMPrime
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentU62
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO10Cent

public section

namespace CFSG.AGLEmbedding

theorem kFactU62OmegaTenThreeCentAut : KFactU62OmegaTenThreeCentAut := by
  intro L _ _ d hd he x hx
  rcases hd with hd | hd
  · exact U62O10Cent.u62ThreeCentAut hd he hx
  · exact O10Cent.o10ThreeCentAut hd he hx

end CFSG.AGLEmbedding

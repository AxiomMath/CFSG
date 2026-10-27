module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Ru
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Tight
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Tight
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.Setup.Family

theorem noSporadicComponentHeJ4
    (hLayer : ActorLayerProp) (hTrans : ComponentTransferProp)
    (hSec : IrreducibleSectionProp) (hHe : SporadicExclusion .He)
    (hJ4 : SporadicExclusion .J4) : NoSporadicComponentProp :=
  noSporadicComponent_of CFSG.SectionRank.j4OrderHyp hLayer hTrans hSec
      ⟨sporadicExclusion_M11, sporadicExclusion_M12, sporadicExclusion_M22_of m22TightProp,
          sporadicExclusion_M23, sporadicExclusion_M24_of m24TightProp, sporadicExclusion_of_J1
          j1ExclusionProp, hHe, hJ4⟩ ⟨twoExtensionFor_J2, twoExtensionFor_HS, twoExtensionFor_Ru⟩

end CFSG.QuasithinUnique.Setup.X1

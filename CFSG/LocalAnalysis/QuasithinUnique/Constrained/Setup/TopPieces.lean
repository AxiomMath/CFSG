module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelOrig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeWrap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMinPBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatMinPImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatMinPK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatMinPCampbell
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatAdapter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatQ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockCanon
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockCComp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockCommute
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelSeed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelMinPImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelW
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelAdapter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelQ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelSum
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockType
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockCommute

public section

namespace CFSG.QuasithinUnique.Setup.Top

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Lift

theorem minParabolicBlocks_of_pieces
    (hT : BlockTransferProp) (hJ4 : X1.SporadicExclusion .J4) :
    MinParabolicBlocks :=
  minParabolicBlocks_of_native
      (natural_canonical_of_decomp hT natVleSProp natBaseProp natYProp natMinPBasicProp
          natMinPImageProp natMinPKProp natMinPCampbellProp natResidualProp natAdapterProp natQProp
          natGenProp natSumProp natKernelProp natCanonicalProp natBlockTransportProp natCCompProp
          natCommuteProp)
      (deleted_canonical_of_decomp hT delBaumannProp delBaseProp delSeedProp delH0Prop
          delMinPBasicProp delMinPImageProp delWProp delResidualProp delAdapterProp delQProp
          delGenProp delSumProp delKernelProp delBlockImageProp delBlockCoreProp delBlockTypeProp
          delBlockGenProp delBlockCommuteProp) X1.sporadicExclusion_He hJ4
      primeUnitaryThreeExclusion

end CFSG.QuasithinUnique.Setup.Top

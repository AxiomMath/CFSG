module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockAltNormalizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Sp62FrameLocal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FrameModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenAssembly
public import CFSG.Yardstones.Mdac756b924db.Definitions

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Yardstones.Mdac756b924db

theorem agl81TheoremAKFacts_of_blocks
    (hL28 : KFactBlockL28Rank) (hL28two : KFactBlockL28TwoRank)
    (hPC : KFactBlockPerfectCoreThree) (hSyl : KFactBlockSylowThreeAut)
    (hHA : KFactBlockHeisenbergAut) (hHI : KFactBlockHeisenbergInner)
    (hFI : KFactBlockFieldIndex) : AGL81TheoremAKFacts where
  p1LieOffChar := CFSG.AGLEmbedding.p1ThreeLieOffChar_holds
  klingenSylow := kFactKlingenSylowNormalCyclic_holds
  blockAltNormalizer := citedBlockAltNormalizer_holds
  gl83 := gl83StronglyEmbeddedThreeSolvable_holds
  sp62Frame := kFactSp62Frame_holds
  omega8Frame := kFactOmega8Frame_holds
  blockL28Rank := hL28
  blockL28TwoRank := hL28two
  blockPerfectCoreThree := hPC
  blockSylowThreeAut := hSyl
  blockHeisenbergAut := hHA
  klingenLocal := kFactKlingenLocal_holds
  klingenThreeLocal := kFactKlingenThreeLocal_holds
  klingenFiveLocal := kFactKlingenFiveLocal_holds
  blockHeisenbergInner := hHI
  klingenIdent := kFactKlingenIdent_holds
  blockFieldIndex := hFI

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

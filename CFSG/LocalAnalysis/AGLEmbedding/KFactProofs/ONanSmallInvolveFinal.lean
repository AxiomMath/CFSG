module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallInvolve
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadAltTwoP
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadJ4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadLinThreeFour
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadM11
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadTits
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbedding

section Witnesses

theorem smallBadNonComm : SmallBadNonComm where
  altTwoP := KFactProofs.SmallBad.AltTwoP.not_normalizerQuotientComm_altTwoP
  linThreeFour _ hL := KFactProofs.SmallBad.L34.not_normalizerQuotientComm_linThreeFour hL
  m11 _ hL := KFactProofs.SmallBad.M11.not_normalizerQuotientComm_m11 hL
  tits _ hL := KFactProofs.SmallBad.Tits.not_normalizerQuotientComm_isTits hL
  mcl hs hL := KFactProofs.SmallBad.McL.not_normalizerQuotientComm_isMcL hs hL
  fi22 hs hL := KFactProofs.SmallBad.Fi22.not_normalizerQuotientComm_isFi22 hs hL
  j4 hs hL := KFactProofs.SmallBad.J4.not_normalizerQuotientComm_isJ4 hs hL

end Witnesses

end CFSG.AGLEmbedding

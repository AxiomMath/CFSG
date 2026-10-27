module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPShape
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NoSPDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem d1CaseTwoShape_of {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hL2 : KFactCaseTwoLocal)
    (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier) (hSyl : KFactCaseTwoSylow)
    (hNo2 : KFactCaseTwoNoTwo) : D1CaseTwoShape G := fun _ _ _ _ _ _ hd _ hz hnSP hout =>
  hd.toAt.czShape (kFactCycAut_of_kFactOutCyclic hOut) hS hL2 hInv.toIn hSch hSyl hNo2 hz hnSP
    hout
end CFSG.LocalAnalysis.RankThreeTheoremC

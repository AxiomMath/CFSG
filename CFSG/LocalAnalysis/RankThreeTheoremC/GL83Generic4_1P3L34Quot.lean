module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

abbrev L34Quot (x : G) (J : Subgroup G) : Type :=
  GenericReduced 3 x ⧸ (reducedCentralizerOfJ x J).normalCore

@[expose] def l34Hom (x : G) (J : Subgroup G) : ↥(centralizer ({x} : Set G)) →* L34Quot x J :=
  (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).comp
    (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3))

@[expose] def l34Img (x : G) (J A : Subgroup G) : Subgroup (L34Quot x J) :=
  (A.subgroupOf (centralizer ({x} : Set G))).map (l34Hom x J)

end CFSG.LocalAnalysis.RankThreeTheoremC

module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaPU

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure D2L34BetaConf (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) : Prop where
  l34 : IsL34Index d
  glob : D2Global G
  d1 : D1For G
  esc : D2Escape 3 P M A H R
  max : D2EscapeMax 3 P M R
  beta : 3 ∈ GLBBetaFour G
  rbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))
  almostSimple : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
    ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
    (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K
  iso : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)
  le_K : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K
  not_centralizer_le : ¬ Subgroup.centralizer
      (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) 3)) ≤
    (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))
  ne : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H
  normalizer_eq : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M
  char : ∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
    (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧ H ≤ Subgroup.normalizer (C : Set G)

@[expose] def D2L34AllResidue (P : Sylow 3 G) (M : Subgroup G) : Prop :=
  ∀ A' H' R' : Subgroup G, D2Escape 3 P M A' H' R' → D2EscapeMax 3 P M R' →
    ∃ (d' : TauCeti.ValidLieTypeIndex) (Rbar' : Sylow 3 (H' ⧸ primeComplementCore (G := H') 3))
      (K' : Subgroup (H' ⧸ primeComplementCore (G := H') 3)),
      D2L34BetaConf d' P M A' H' R' Rbar' K'

@[expose] def D2L34BetaResidueU : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    D2L34AllResidue P M → False

theorem D2L34BetaConf.of_l34 (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hNO : KFactL34NotOrthogonal) (hSch : KFactCatalogSchreier)
    (hNS : KFactL34NormalizerSolvable) (h84 : Asc81bEightFour) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hS3 : D2PairStrongThree) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) (hglob : D2Global G) (hD1 : D1For G) {P : Sylow 3 G}
    {M A H R : Subgroup G} (hesc : D2Escape 3 P M A H R) (hmax : D2EscapeMax 3 P M R)
    (hβ : 3 ∈ GLBBetaFour G) {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    D2L34BetaConf d P M A H R Rbar K := by
  have hAK := hK.le_of_l34 hO hd he
  have hC := hesc.not_centralizer_le_of_l34 hI h84 hD2 hS3 hd hglob hD1 hmax hβ hK he hAK
  obtain ⟨htwo, hNT, hch⟩ :=
    hesc.l34ResidueData hI hNO hSch hNS h84 h93 hD2 hS3 hd hglob hD1 hmax hβ hK he hAK
  exact ⟨hd, hglob, hD1, hesc, hmax, hβ, hRbar, hK, he, hAK, hC, htwo, hNT, hch⟩

theorem d2L34AllResidue_of_onlyL34At (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hNO : KFactL34NotOrthogonal) (hSch : KFactCatalogSchreier)
    (hNS : KFactL34NormalizerSolvable) (h84 : Asc81bEightFour) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hS3 : D2PairStrongThree) (hglob : D2Global G) (hD1 : D1For G)
    (hβ : 3 ∈ GLBBetaFour G) {P : Sylow 3 G} {M : Subgroup G} (hX : D2OnlyL34At P M) :
    D2L34AllResidue P M := by
  intro A' H' R' hesc hmax
  obtain ⟨Rbar', K', hRbar', hK'⟩ := hesc.almostSimple hglob.toAGLGlobal
  obtain ⟨d', hd', he'⟩ := hX A' H' R' hesc hmax Rbar' K' hRbar' hK'
  exact ⟨d', Rbar', K', D2L34BetaConf.of_l34 hO hI hNO hSch hNS h84 h93 hD2 hS3 hd' hglob hD1
    hesc hmax hβ hRbar' hK' he'⟩

theorem D2L34AllResidue.onlyL34At {P : Sylow 3 G} {M : Subgroup G} (h : D2L34AllResidue P M) :
    D2OnlyL34At P M := by
  intro A' H' R' hesc hmax Rbar' K' _ hK'
  obtain ⟨d', Rbar'', K'', hc⟩ := h A' H' R' hesc hmax
  have hKK : K' = K'' := hc.almostSimple.unique K' hK'.component
  subst hKK
  exact ⟨d', hc.l34, hc.iso⟩

theorem d2L34BetaCase_of_residueU (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hNO : KFactL34NotOrthogonal) (hSch : KFactCatalogSchreier)
    (hNS : KFactL34NormalizerSolvable) (h84 : Asc81bEightFour) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hS3 : D2PairStrongThree) (hRes : D2L34BetaResidueU) :
    D2L34BetaCase := by
  intro d hd G _ _ hglob hD1 P M A H R hesc hmax hβ Rbar K hRbar hK he hAK hC hX
  obtain ⟨htwo, hNT, hch⟩ :=
    hesc.l34ResidueData hI hNO hSch hNS h84 h93 hD2 hS3 hd hglob hD1 hmax hβ hK he hAK
  exact hRes d G P M A H R Rbar K
    ⟨hd, hglob, hD1, hesc, hmax, hβ, hRbar, hK, he, hAK, hC, htwo, hNT, hch⟩
    (d2L34AllResidue_of_onlyL34At hO hI hNO hSch hNS h84 h93 hD2 hS3 hglob hD1 hβ hX)

end CFSG.AGLEmbeddingD2

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

structure D2L34BetaConf3 (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) : Prop where
  l34 : IsL34Index d
  esc : D2Escape 3 P M A H R
  max : D2EscapeMax 3 P M R
  rbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))
  almostSimple : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
    ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
    (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K
  iso : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)
  le_K : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K
  not_centralizer_le : ¬ Subgroup.centralizer
      (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) 3)) ≤
    (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))
  ne : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H
  normalizer_eq : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M
  char : ∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
    (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧ H ≤ Subgroup.normalizer (C : Set G)

class D2Amb3 (G : Type) [Group G] [Finite G] : Prop where
  glob : AGLGlobal G
  d1 : D1At G 3

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.AGLEmbeddingD2

open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

theorem D2L34BetaConf.toConf3 {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hc : D2L34BetaConf d P M A H R Rbar K) :
    CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3 d P M A H R Rbar K :=
  ⟨hc.l34, hc.esc, hc.max, hc.rbar, hc.almostSimple, hc.iso, hc.le_K, hc.not_centralizer_le,
    hc.ne, hc.normalizer_eq, hc.char⟩

theorem D2L34BetaConf.amb3 {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hc : D2L34BetaConf d P M A H R Rbar K) :
    CFSG.LocalAnalysis.RankThreeTheoremC.D2Amb3 G :=
  ⟨hc.glob.toAGLGlobal, hc.d1 3 hc.beta⟩

end CFSG.AGLEmbeddingD2

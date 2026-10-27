module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2AltFive3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveBlocks
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG
open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

@[expose] def D2AltFiveBlock3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (p : ℕ) [Fact p.Prime], p ∈ rankThreeSigmaA G → p = 5 →
    ∀ (P : Sylow p G) (A H : Subgroup G), IsCoreMaxLocal p P M → D2Escape p P M A H A →
    D2EscapeMax p P M A →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* alternatingGroup (Fin (2 * p))) →
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        ¬ barM M A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → False

theorem d2AltFiveBlock3_of (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hX : D1NoXBlock3 G) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKB : KFactBlockAltFiveSectionInner) (hKS : KFactBlockAltFiveSquareInner) :
    D2AltFiveBlock3 G := by
  intro hS hD1' M hM hfc hthree p _ hσ hp5 P A H hcore hesc hmax Rbar K hRbar hK ⟨e⟩ L hL hA
  subst hp5
  have hM3 : Open.pRank 3 M ≤ 3 := by
    have := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) M hesc.maxTwoLocal_M.1
    rwa [hS.rank] at this
  exact false_of_altFiveBlock hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKB hKS
    (aglGlobal_of_setting hS) (d1For_of_setting hS) (noXBlockFor_of_setting hX hS) hesc hRbar hK e
    hM3 hL hA

@[expose] def D2AltFiveResidue3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (p : ℕ) [Fact p.Prime], p ∈ rankThreeSigmaA G → p = 5 →
    ∀ (P : Sylow p G) (A H : Subgroup G), IsCoreMaxLocal p P M → D2Escape p P M A H A →
    D2EscapeMax p P M A →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* alternatingGroup (Fin (2 * p))) →
      ((∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧
          ¬ barM M A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∨
        ∃ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ ∧
          barM M A ⊓ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) → False

theorem d2AltFiveResidue3_of_block (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hX : D1NoXBlock3 G)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hblock : D2AltFiveBlock3 G) : D2AltFiveResidue3 G := by
  intro hS hD1' M hM hfc hthree p _ hσ hp5 P A H hcore hesc hmax Rbar K hRbar hK ⟨e⟩ hres
  exact false_of_altFiveResidue hα hSch h85 h86 h93 hK2 hC3 hK5 (aglGlobal_of_setting hS)
    (d1For_of_setting hS) (noXBlockFor_of_setting hX hS) hp5 hesc hRbar hK e
    (fun L hL hA => hblock hS hD1' M hM hfc hthree p hσ hp5 P A H hcore hesc hmax Rbar K hRbar hK
      ⟨e⟩ L hL hA) hres

theorem d2AltFive3_of_residue3 (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hX : D1NoXBlock3 G) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hres : D2AltFiveResidue3 G) : D2AltFive3 G := by
  intro hS hD1' M hM hfc hthree p _ hσ hp5 P A H hcore hesc hmax Rbar K hRbar hK ⟨e⟩
  exact hres hS hD1' M hM hfc hthree p hσ hp5 P A H hcore hesc hmax Rbar K hRbar hK ⟨e⟩
    (altFiveResidue_of_escape hα hSch h84 h85 h86 h93 hK2 hC3 hK5 (aglGlobal_of_setting hS)
      (d1For_of_setting hS) (noXBlockFor_of_setting hX hS) hp5 hesc hRbar hK e)


theorem d2AltFive3_of_blockFacts (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hX : D1NoXBlock3 G) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKB : KFactBlockAltFiveSectionInner) (hKS : KFactBlockAltFiveSquareInner) :
    D2AltFive3 G :=
  d2AltFive3_of_residue3 hα hSch h84 h85 h86 h93 hX hK2 hC3 hK5
    (d2AltFiveResidue3_of_block hα hSch h85 h86 h93 hX hK2 hC3 hK5
      (d2AltFiveBlock3_of hα hSch h84 h85 h86 h93 hX hK2 hC3 hK5 hKB hKS))

end CFSG.LocalAnalysis.RankThreeTheoremC

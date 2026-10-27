module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Leaves3
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.TransCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Families3Heis

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2TransMSide3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (p : ℕ) [Fact p.Prime], p ∈ rankThreeSigmaA G → 5 ≤ p →
    ∀ (P : Sylow p G) (A H R : Subgroup G), IsCoreMaxLocal p P M → D2Escape p P M A H R →
    D2EscapeMax p P M R →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p))
      (zb : H ⧸ primeComplementCore (G := H) p),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      D2TransBorel p Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K zb →
      CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

theorem d2TransMSide3_of (hX : D1NoXBlock3 G) (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime) : D2TransMSide3 G := by
  intro hS hD1 M hM ha hb p _ hp hp5 P A H R hMP hesc _ Rbar K zb hRbar hK hB
  exact hesc.pCore_ne_bot_of_transBorel hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKin hKP hC3p hK5p
    (aglGlobal_of_setting hS) (d1For_of_setting hS) (noXBlockFor_of_setting hX hS) hp5 hRbar hK hB

theorem D2KFactLeaves.transMSide3 (hK : D2KFactLeaves) : D2TransMSide3 G :=
  d2TransMSide3_of hK.noXBlock3 hK.threeOrFiveDvd hK.catalogSchreier hK.eightFour hK.eightFive
    hK.eightSix hK.nineThree hK.parabolicThree hK.citedBlockThree hK.blockThreeAltSeven
    hK.twoGenInner hK.parabolicPrime hK.citedBlockPrime hK.blockAltSevenPrime

theorem d2IndexCaseAt3_sz32_five (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (hMS : D2TransMSide3 G) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hX : D1NoXBlock3 G)
    (hSzB : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2TransBorelAt (.lie d) fun p => p = 5)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusBorelAt (.lie d) fun p => p = 5)
    (hHS : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hMcL : D2HeisLocalEqAt (.sporadic .McL) fun p => p = 5)
    (hSpor : ∀ s : TauCeti.SporadicName, s ≠ .HS → s ≠ .McL →
      D2IndexCaseAt3 G (.sporadic s) fun p => p = 5)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .suzuki 2) :
    D2IndexCaseAt3 G (.lie d) fun p => p = 5 := by
  intro hSet hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
  subst hpp
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨zb, hB⟩ := hSzB d hd _ 5 rfl Rbar _ _ K hK he
  have hexp : ∃ b ∈ R, b ^ 5 ≠ 1 := exists_pow_ne_one_of_map hRbar hB.exp
  exact hesc.false_of_transBorelFor h84 hCGT (aglGlobal_of_setting hSet)
    (d1At_of_theoremD1 hD1 hp) (noXBlockFor_of_setting hX hSet) hmax
    (fun H' h' => h'.transBorel_of_exp hrank kFactLinThreeCore hS kFactUnitarySylowStructure hSzB
      hTits hHS hMcL (fun s h1 h2 => (hSpor s h1 h2).for hSet hD1 hM ha hb hp rfl hMP hmax)
      (aglGlobal_of_setting hSet) hexp)
    (hMS hSet hD1 M hM ha hb 5 hp (by norm_num) P A H R hMP hesc hmax Rbar K zb hRbar hK hB)

end CFSG.LocalAnalysis.RankThreeTheoremC

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisBorel
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisCase
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore HasPrimeConstraint)

variable {G : Type} [Group G] [Finite G]

theorem D2IndexCaseAt3.for {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop} (h : D2IndexCaseAt3 G i Pp)
    (hS : Setting G) (hD1 : TheoremD1 G) {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (ha : D2FullCoreAt G M) (hb : D2ThreeClauseAt G M) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    (hpp : Pp p) {P : Sylow p G} {A R : Subgroup G} (hMP : IsCoreMaxLocal p P M)
    (hmax : D2EscapeMax p P M R) : D2IndexCaseFor p P M A R i :=
  fun H hesc Rbar K hRbar hK he =>
    h hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he

@[expose] def D2HeisMSide3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (p : ℕ) [Fact p.Prime], p ∈ rankThreeSigmaA G → 5 ≤ p →
    ∀ (P : Sylow p G) (A H R : Subgroup G), IsCoreMaxLocal p P M → D2Escape p P M A H R →
    D2EscapeMax p P M R →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      D2HeisBorel p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal

theorem d2HeisMSide3_of (hX : D1NoXBlock3 G) (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime) : D2HeisMSide3 G := by
  intro hS hD1 M hM ha hb p _ hp hp5 P A H R hMP hesc _ Rbar K hRbar hK hB
  exact hesc.normal_sup_of_heisBorel hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKin hKP hC3p hK5p
    (aglGlobal_of_setting hS) (d1For_of_setting hS) (noXBlockFor_of_setting hX hS) hp5 hRbar hK hB

theorem d2IndexCaseAt3_of_heisBorel (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (HB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt3 G (.lie d) fun p => IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt3 G (.sporadic s) fun p => ¬ HB (.sporadic s) p)
    (hMS : D2HeisMSide3 G) (hCGT : AschbacherLocalCGTBlock) (hX : D1NoXBlock3 G)
    {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop} (hiB : D2HeisBorelAt i Pp)
    (hp5 : ∀ p, Pp p → 5 ≤ p) : D2IndexCaseAt3 G i Pp := by
  intro hSet hD1 M hM ha hb p hp hpc P A H R hMP hesc hmax Rbar K hRbar hK he
  have : Fact p.Prime := ⟨hesc.prime⟩
  have hB := hiB _ p hpc Rbar _ _ K hK he
  exact hesc.false_of_heisBorelFor hrank kFactLinThreeCore hS unitaryBorelKFacts HB hHB
    (fun d hd hb' => (hexc d).for hSet hD1 hM ha hb hp ⟨hd, hb'⟩ hMP hmax)
    (fun s hb' => (hSpor s).for hSet hD1 hM ha hb hp hb' hMP hmax) hCGT
    (aglGlobal_of_setting hSet) (d1At_of_theoremD1 hD1 hp) (noXBlockFor_of_setting hX hSet) hmax
    (hp5 p hpc) hRbar hB
    (hMS hSet hD1 M hM ha hb p hp (hp5 p hpc) P A H R hMP hesc hmax Rbar K hRbar hK hB)

end CFSG.LocalAnalysis.RankThreeTheoremC

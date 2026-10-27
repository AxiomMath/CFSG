module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSevenPrime
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisBorel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Case
import CFSG.LocalAnalysis.AGLEmbeddingD2.CompetitorR
import CFSG.LocalAnalysis.AGLEmbeddingD2.Roadmap

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem D2Escape.aglJConfig_of_heisLeavesFor {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M A H R : Subgroup G} (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (hKU : UnitaryBorelKFacts) (HB : TauCeti.CFSGIndex → ℕ → Prop)
    (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex, IsD2SeitzException p d.1 → ¬ HB (.lie d) p →
      D2IndexCaseFor p P M A R (.lie d))
    (hSpor : ∀ s : TauCeti.SporadicName, ¬ HB (.sporadic s) p →
      D2IndexCaseFor p P M A R (.sporadic s))
    (hglob : AGLGlobal G) (h : D2Escape p P M A H R) (hp5 : 5 ≤ p) (hcard : Nat.card R = p ^ 3)
    (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal) : AGLJConfig p M H R R := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine h.aglJConfig_of_cases hrank hL3 hKU hglob hp5 hcard hRQ
    (fun Rbar K hRbar hK s hi => ?_) fun Rbar K hRbar hK d hchar ⟨e⟩ => ?_
  · by_cases hB : HB (.sporadic s) p
    · exact h.aglJConfig_of_borel hglob hRbar (hHB _ _ p hB Rbar _ _ K hK hi) hRQ
    · exact (hSpor s hB H h Rbar K hRbar hK hi).elim
  · by_cases hexcp : IsD2SeitzException p d.1
    · by_cases hB : HB (.lie d) p
      · exact h.aglJConfig_of_borel hglob hRbar (hHB _ _ p hB Rbar _ _ K hK ⟨e⟩) hRQ
      · exact (hexc d hexcp hB H h Rbar K hRbar hK ⟨e⟩).elim
    · exact (hK.false_of_seitzCross hS d e hchar hexcp).elim

theorem D2Escape.false_of_heisBorelFor {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M A H R : Subgroup G} (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (hKU : UnitaryBorelKFacts) (HB : TauCeti.CFSGIndex → ℕ → Prop)
    (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex, IsD2SeitzException p d.1 → ¬ HB (.lie d) p →
      D2IndexCaseFor p P M A R (.lie d))
    (hSpor : ∀ s : TauCeti.SporadicName, ¬ HB (.sporadic s) p →
      D2IndexCaseFor p P M A R (.sporadic s))
    (hCGT : AschbacherLocalCGTBlock) (hglob : AGLGlobal G) (hD1p : D1At G p)
    (hX : NoXBlockFor G) (h : D2Escape p P M A H R) (hmax : D2EscapeMax p P M R) (hp5 : 5 ≤ p)
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hB : D2HeisBorel p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal) : False := by
  have hcard : Nat.card R = p ^ 3 := by
    rw [← h.card_map_eq le_rfl, ← hRbar]
    exact hB.card
  refine false_of_agljCompetitorsOn (p := p) (M := M) (R := R) (X := R)
    (C := fun H' => D2Escape p P M A H' R ∧ (⊥ : Subgroup G) ≤ nclIn H' R) ?_
    (agljCompetitorsOn_d2Escape hmax hglob hD1p) ⟨h, bot_le⟩ hCGT hX
  rintro H' ⟨h', -⟩
  exact h'.aglJConfig_of_heisLeavesFor hrank hL3 hS hKU HB hHB hexc hSpor hglob hp5 hcard hRQ

theorem d2IndexCaseAt_of_heisBorel (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (hKU : UnitaryBorelKFacts) (HB : TauCeti.CFSGIndex → ℕ → Prop)
    (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt (.sporadic s) fun p => ¬ HB (.sporadic s) p)
    (hMS : D2HeisMSide) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop} (hiB : D2HeisBorelAt i Pp)
    (hp5 : ∀ p, Pp p → 5 ≤ p) : D2IndexCaseAt i Pp := by
  intro G _ _ hglob hD1 p hpc P M A H R hesc hmax hβ Rbar K hRbar hK he
  have : Fact p.Prime := ⟨hesc.prime⟩
  have hB := hiB _ p hpc Rbar _ _ K hK he
  exact hesc.false_of_heisBorelFor hrank hL3 hS hKU HB hHB
    (fun d hd hb => (hexc d).for hglob hD1 ⟨hd, hb⟩ hmax hβ)
    (fun s hb => (hSpor s).for hglob hD1 hb hmax hβ) hCGT hglob.toAGLGlobal (hD1.at hβ)
    (hD2.noXBlockFor hglob.toD1Global) hmax (hp5 p hpc) hRbar hB
    (hMS G hglob hD1 p (hp5 p hpc) P M A H R hesc hmax hβ Rbar K hRbar hK hB)

theorem d2ComponentCase_of_heis (hrank : KFactLieCharRank) (hS : D2SeitzCross)
    (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hAlt5 : D2AltFive) (hA6 : D2AltSixCase) (hThree : D2U3Three)
    (HB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hHB5 : ∀ i p, HB i p → 5 ≤ p)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt (.sporadic s) fun p => ¬ HB (.sporadic s) p) : D2ComponentCase := by
  have hMS : D2HeisMSide :=
    d2HeisMSide_of hα hSch h84 h85 h86 h93 hD2 hK2 hC3 hK5 hKin hKP hC3p hK5p
  have hHBcase : ∀ i, D2IndexCaseAt i (HB i) := fun i =>
    d2IndexCaseAt_of_heisBorel hrank kFactLinThreeCore hS unitaryBorelKFacts HB hHB hexc hSpor hMS
      hCGT hD2 (hHB i) (hHB5 i)
  refine d2ComponentCase_of_current hrank hS hSch hα h84 h85 h86 h93 hCGT hD2 hK2 hC3 hK5 hKin hKP
    hC3p hK5p hAlt5 hA6 hThree ?_ fun s => d2IndexCase_of_cases (hHBcase (.sporadic s)) (hSpor s)
  intro d G _ _ hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he
  by_cases hB : HB (.lie d) p
  · exact hHBcase (.lie d) G hglob hD1 p hB P M A H R hesc hmax hβ Rbar K hRbar hK he
  · exact hexc d G hglob hD1 p ⟨hp, hB⟩ P M A H R hesc hmax hβ Rbar K hRbar hK he

end CFSG.AGLEmbeddingD2

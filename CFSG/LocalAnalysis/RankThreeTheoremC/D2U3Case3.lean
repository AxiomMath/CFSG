module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Case
import CFSG.LocalAnalysis.AGLEmbeddingD2.CompetitorR
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore HasPrimeConstraint)

@[expose] def D2U3Three3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    D2IndexCaseAt3 G (.lie d) fun p => p = d.1.characteristic ∧ p = 3

section Escape

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem d2Escape_normal_sup_of_u3 [Fact p.Prime] (hSet : Setting G) (hX : D1NoXBlock3 G)
    (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (h : D2Escape p P M A H R)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) (hp5 : 5 ≤ p) : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal :=
  h.normal_sup_of_u3 unitaryBorelKFacts hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKin hKP hC3p hK5p
    (aglGlobal_of_setting hSet) (d1For_of_setting hSet) (noXBlockFor_of_setting hX hSet) hRbar hK hd
    hn e hp5

theorem d2Escape_aglJConfig_of_leaves3 (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (hexc : D2SeitzExc3 G) (hSpor : D2SporadicCase3 G) (hSet : Setting G) (hD1 : TheoremD1 G)
    (hM : rankThreeIsMaxTwoLocal M) (ha : D2FullCoreAt G M) (hb : D2ThreeClauseAt G M)
    (hp : p ∈ rankThreeSigmaA G) (hMP : IsCoreMaxLocal p P M) (h : D2Escape p P M A H R)
    (hmax : D2EscapeMax p P M R) (hp5 : 5 ≤ p) (hcard : Nat.card R = p ^ 3)
    (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal) : AGLJConfig p M H R R := by
  refine h.aglJConfig_of_cases hrank kFactLinThreeCore unitaryBorelKFacts
    (aglGlobal_of_setting hSet) hp5 hcard hRQ
    (fun Rbar K hRbar hK s hi =>
      (hSpor s hSet hD1 M hM ha hb p hp trivial P A H R hMP h hmax Rbar K hRbar hK hi).elim)
    fun Rbar K hRbar hK d hchar ⟨e⟩ => ?_
  by_cases hexcp : IsD2SeitzException p d.1
  · exact (hexc d hSet hD1 M hM ha hb p hp hexcp P A H R hMP h hmax Rbar K hRbar hK ⟨e⟩).elim
  · exact (hK.false_of_seitz hS d e hchar hexcp).elim

end Escape

variable {G : Type} [Group G] [Finite G]

theorem d2CaseU33_of (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (hexc : D2SeitzExc3 G) (hSpor : D2SporadicCase3 G) (hThree : D2U3Three3 G)
    (hX : D1NoXBlock3 G) (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hCGT : AschbacherLocalCGTBlock) : D2CaseU33 G := by
  intro d hd hSet hD1 M hM ha hb p hp hpc P A H R hMP hesc hmax Rbar K hRbar hK he
  by_cases hp3 : p = 3
  · exact hThree d hd hSet hD1 M hM ha hb p hp ⟨hpc, hp3⟩ P A H R hMP hesc hmax Rbar K hRbar hK he
  have hprime : p.Prime := hesc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hp5 : 5 ≤ p := by
    have := hprime.two_le
    have := hesc.ne_two
    rcases (show p = 4 ∨ 5 ≤ p by omega) with h4 | h5
    · exact absurd (h4 ▸ hprime) (by norm_num)
    · exact h5
  obtain ⟨e⟩ := he
  obtain ⟨hdu, hnu⟩ := isUnitaryIndex_of_case hpc hd
  have hcard : Nat.card R = p ^ 3 := hesc.card_eq_of_u3 hRbar hK hdu hnu e
  have hRQ := d2Escape_normal_sup_of_u3 hSet hX hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKin hKP hC3p
    hK5p hesc hRbar hK hdu hnu e hp5
  refine false_of_agljCompetitorsOn (p := p) (M := M) (R := R) (X := R)
    (C := fun H' => D2Escape p P M A H' R ∧ (⊥ : Subgroup G) ≤ nclIn H' R) ?_
    (agljCompetitorsOn_d2Escape hmax (aglGlobal_of_setting hSet) (d1At_of_theoremD1 hD1 hp))
    ⟨hesc, bot_le⟩ hCGT (noXBlockFor_of_setting hX hSet)
  rintro H' ⟨h', -⟩
  exact d2Escape_aglJConfig_of_leaves3 hrank hS hexc hSpor hSet hD1 hM ha hb hp hMP h' hmax hp5
    hcard hRQ

end CFSG.LocalAnalysis.RankThreeTheoremC

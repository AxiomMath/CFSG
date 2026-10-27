module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3MSide
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCase
import CFSG.LocalAnalysis.AGLEmbeddingD2.CompetitorR
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryUnipotentCentralizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCharCases

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem D2Escape.false_of_A_eq_of_card {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M A H R : Subgroup G} (h : D2Escape p P M A H R) (hcard : Nat.card R = p ^ 3)
    (hAR : A = R) : False := by
  subst hAR
  rw [h.card_A] at hcard
  have := Nat.pow_right_injective h.prime.two_le hcard
  omega

theorem D2Escape.aglJConfig_of_cases {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M A H R : Subgroup G} (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hKU : UnitaryBorelKFacts) (hglob : AGLGlobal G) (h : D2Escape p P M A H R) (hp5 : 5 ≤ p)
    (hcard : Nat.card R = p ^ 3) (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal)
    (hspor : ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      ∀ s : TauCeti.SporadicName, Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
        AGLJConfig p M H R R)
    (hcross : ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      ∀ d : TauCeti.ValidLieTypeIndex, p ≠ d.1.characteristic →
        Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → AGLJConfig p M H R R) :
    AGLJConfig p M H R R := by
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Rbar, K, hRbar, hK⟩ := h.almostSimple hglob
  obtain ⟨i, hi⟩ := hK.catalog
  cases i with
  | cyclic q hq => exact (d2IndexCaseFor_cyclic q hq H h Rbar K hRbar hK hi).elim
  | sporadic s => exact hspor Rbar K hRbar hK s hi
  | alternating n hn =>
    exfalso
    obtain ⟨e⟩ := hi
    have hn2 : n = 2 * p := hK.eq_two_mul_of_alternating hn e
    subst hn2
    have hRA := hK.sylow_eq_of_alternating hp5 e
    rw [hRbar] at hRA
    exact h.false_of_A_eq_of_card hcard (h.A_eq_of_map_eq hRA)
  | lie d =>
    by_cases hchar : p = d.1.characteristic
    · obtain ⟨e⟩ := hi
      obtain ⟨q, hqp, hq⟩ := hK.lieChar_cases hrank hL3 d e hchar
      rcases hq with ⟨hq2, hd⟩ | ⟨hq1, hd⟩
      · obtain ⟨e'⟩ :=
          nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := p) (n := 2) ⟨q, hd, hqp, hq2⟩
        exact (h.false_of_A_eq_of_card hcard (h.A_eq_of_psl2 hRbar hK (e.trans e'))).elim
      · obtain ⟨hdu, hnu⟩ := isUnitaryIndex_of_twistedA hqp hq1 hd
        exact h.aglJConfig_of_u3 hKU hglob hRbar hK hdu hnu e hRQ
    · exact hcross Rbar K hRbar hK d hchar hi

theorem D2Escape.aglJConfig_of_leaves {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M A H R : Subgroup G} (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (hKU : UnitaryBorelKFacts)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => IsD2SeitzException p d.1)
    (hSpor : D2SporadicCase) (hglob : D2Global G) (hD1 : D1For G)
    (h : D2Escape p P M A H R) (hmax : D2EscapeMax p P M R) (hβ : p ∈ GLBBetaFour G)
    (hp5 : 5 ≤ p) (hcard : Nat.card R = p ^ 3)
    (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal) : AGLJConfig p M H R R := by
  refine h.aglJConfig_of_cases hrank hL3 hKU hglob.toAGLGlobal hp5 hcard hRQ
    (fun Rbar K hRbar hK s hi =>
      (hSpor s G hglob hD1 p P M A H R h hmax hβ Rbar K hRbar hK hi).elim)
    fun Rbar K hRbar hK d hchar ⟨e⟩ => ?_
  by_cases hexcp : IsD2SeitzException p d.1
  · exact (hexc d G hglob hD1 p hexcp P M A H R h hmax hβ Rbar K hRbar hK ⟨e⟩).elim
  · exact (hK.false_of_seitzCross hS d e hchar hexcp).elim

@[expose] def D2U3Three : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    D2IndexCaseAt (.lie d) fun p => p = d.1.characteristic ∧ p = 3

theorem unitaryBorelKFacts : UnitaryBorelKFacts :=
  ⟨kFactUnitarySylowStructure, kFactUnitaryUnipotentCentralizer, kFactUnitaryBorelMaximal,
    kFactUnitarySylowNormalizerSolvable⟩

theorem d2CaseU3_of (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore) (hS : D2SeitzCross)
    (hKU : UnitaryBorelKFacts) (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => IsD2SeitzException p d.1)
    (hSpor : D2SporadicCase) (hMS : D2U3MSide) (hThree : D2U3Three)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : D2CaseU3 := by
  intro d hd G _ _ hglob hD1 p hpc P M A H R hesc hmax hβ Rbar K hRbar hK he
  by_cases hp3 : p = 3
  · exact hThree d hd G hglob hD1 p ⟨hpc, hp3⟩ P M A H R hesc hmax hβ Rbar K hRbar hK he
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
  have hRQ := hMS G hglob hD1 p hp5 P M A H R hesc hmax hβ Rbar K hRbar hK d hdu hnu ⟨e⟩
  refine false_of_agljCompetitorsOn (p := p) (M := M) (R := R) (X := R)
    (C := fun H' => D2Escape p P M A H' R ∧ (⊥ : Subgroup G) ≤ nclIn H' R) ?_
    (agljCompetitorsOn_d2Escape hmax hglob.toAGLGlobal (hD1.at hβ)) ⟨hesc, bot_le⟩ hCGT
    (hD2.noXBlockFor hglob.toD1Global)
  rintro H' ⟨h', -⟩
  exact h'.aglJConfig_of_leaves hrank hL3 hS hKU hexc hSpor hglob hD1 hmax hβ hp5 hcard hRQ

end CFSG.AGLEmbeddingD2

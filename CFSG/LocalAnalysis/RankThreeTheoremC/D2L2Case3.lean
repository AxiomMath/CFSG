module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LieAlt3
import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorsLeaves
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Case

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore HasPrimeConstraint)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2SurvivorFacts3 (p : ℕ) (M A H : Subgroup G) : Prop :=
  D2XSurvivor ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))

theorem d2SurvivorFacts3_of_leaves (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (hexc : D2SeitzExc3 G) (hSpor : D2SporadicCase3 G) (hSet : Setting G) (hD1 : TheoremD1 G)
    {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) (ha : D2FullCoreAt G M)
    (hb : D2ThreeClauseAt G M) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {A H : Subgroup G} (hMP : IsCoreMaxLocal p P M) (hesc : D2Escape p P M A H A)
    (hmax : D2EscapeMax p P M A) : D2SurvivorFacts3 p M A H := by
  have : Fact p.Prime := ⟨hesc.prime⟩
  obtain ⟨Rbar, K, hRbar, hK⟩ := d2Escape_almostSimple3 hSet hesc
  have hX := hK.xSurvivor_of_cases hRbar hrank kFactLinThreeCore
    (fun q hq hi => d2IndexCase3_cyclic q hq hSet hD1 M hM ha hb p hp trivial P A H A hMP hesc hmax
      Rbar K hRbar hK hi)
    (fun s hi => (hSpor s hSet hD1 M hM ha hb p hp trivial P A H A hMP hesc hmax Rbar K hRbar hK
      hi).elim)
    fun d hchar ⟨e⟩ => by
      by_cases hexcp : IsD2SeitzException p d.1
      · exact (hexc d hSet hD1 M hM ha hb p hp hexcp P A H A hMP hesc hmax Rbar K hRbar hK
          ⟨e⟩).elim
      · exact (hK.false_of_seitz hS d e hchar hexcp).elim
  obtain ⟨hD, hC⟩ := hX
  exact ⟨hD, hRbar ▸ hC⟩

@[expose] def D2TheoremZ3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (A H : Subgroup G),
    IsCoreMaxLocal p P M → D2Escape p P M A H A → D2EscapeMax p P M A →
    (∀ H' : Subgroup G, D2Escape p P M A H' A → D2SurvivorFacts3 p M A H') →
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥ → False

@[expose] def D2L2MSide3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (p : ℕ) [Fact p.Prime], p ∈ rankThreeSigmaA G → 5 ≤ p →
    ∀ (P : Sylow p G) (A H : Subgroup G), IsCoreMaxLocal p P M → D2Escape p P M A H A →
    D2EscapeMax p P M A →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* PSL2GF p 2) → CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

theorem d2CaseL2Square3_of_leaves (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (hexc : D2SeitzExc3 G) (hSpor : D2SporadicCase3 G) (hZ : D2TheoremZ3 G)
    (hMS : D2L2MSide3 G) : D2CaseL2Square3 G := by
  intro d ⟨q, hq2, hd⟩ hSet hD1 M hM ha hb p hp hpc P A H R hMP hesc hmax Rbar K hRbar hK ⟨e⟩
  have hprime : p.Prime := hesc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hqp : q.p = p := by rw [hpc, hd, TauCeti.LieTypeIndex.characteristic_A]
  obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := p) (n := 2) ⟨q, hd, hqp, hq2⟩
  have hp5 : 5 ≤ p := hqp ▸ five_le_of_valid_A_one hd hq2 (hqp ▸ hesc.ne_two)
  have hAR : A = R := hesc.A_eq_of_psl2 hRbar hK (e.trans e')
  subst hAR
  exact hZ hSet hD1 M hM ha hb p hp P A H hMP hesc hmax
    (fun H' h' => d2SurvivorFacts3_of_leaves hrank hS hexc hSpor hSet hD1 hM ha hb hp hMP h' hmax)
    (hMS hSet hD1 M hM ha hb p hp hp5 P A H hMP hesc hmax Rbar K hRbar hK ⟨e.trans e'⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC

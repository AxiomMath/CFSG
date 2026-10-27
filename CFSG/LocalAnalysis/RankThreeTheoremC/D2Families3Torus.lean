module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.TorusCase
import CFSG.LocalAnalysis.RankThreeTheoremC.D2TheoremZ3
import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorsLeaves
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore HasPrimeConstraint)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2SurvivorsAll3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (A H : Subgroup G),
    IsCoreMaxLocal p P M → D2Escape p P M A H A → D2EscapeMax p P M A → D2SurvivorFacts3 p M A H

theorem d2SurvivorsAll3_of_heisTorusLeaves (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (HB TB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hTB : ∀ i, D2TorusBorelAt i (TB i))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt3 G (.lie d) fun p =>
        IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p ∧ ¬ TB (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt3 G (.sporadic s) fun p => ¬ HB (.sporadic s) p ∧ ¬ TB (.sporadic s) p) :
    D2SurvivorsAll3 G := by
  intro hSet hD1 M hM ha hb p hp P A H hMP hesc hmax
  have : Fact p.Prime := ⟨hesc.prime⟩
  obtain ⟨Rbar, K, hRbar, hK⟩ := d2Escape_almostSimple3 hSet hesc
  have hnHB : ∀ i, HB i p → Nonempty (K ≃* i.Group) → False := fun i hiB he => by
    have hc := (hHB i _ p hiB Rbar _ _ K hK he).card
    rw [hRbar, hK.card_A] at hc
    have := Nat.pow_right_injective hK.prime.two_le hc
    omega
  have hX := hK.xSurvivor_of_cases hRbar hrank kFactLinThreeCore
    (fun q hq hi => d2IndexCase3_cyclic q hq hSet hD1 M hM ha hb p hp trivial P A H A hMP hesc hmax
      Rbar K hRbar hK hi)
    (fun s hi => by
      by_cases hB : HB (.sporadic s) p
      · exact (hnHB _ hB hi).elim
      by_cases hT : TB (.sporadic s) p
      · exact (hTB _ _ p hT Rbar _ _ K hK hi).xSurvivor
      · exact (hSpor s hSet hD1 M hM ha hb p hp ⟨hB, hT⟩ P A H A hMP hesc hmax Rbar K hRbar hK
          hi).elim)
    fun d hchar ⟨e⟩ => by
      by_cases hexcp : IsD2SeitzException p d.1
      · by_cases hB : HB (.lie d) p
        · exact (hnHB _ hB ⟨e⟩).elim
        by_cases hT : TB (.lie d) p
        · exact (hTB _ _ p hT Rbar _ _ K hK ⟨e⟩).xSurvivor
        · exact (hexc d hSet hD1 M hM ha hb p hp ⟨hexcp, hB, hT⟩ P A H A hMP hesc hmax Rbar K
            hRbar hK ⟨e⟩).elim
      · exact (hK.false_of_seitz hS d e hchar hexcp).elim
  obtain ⟨hD, hC⟩ := hX
  exact ⟨hD, hRbar ▸ hC⟩

@[expose] def D2TorusMSide3 (G : Type) [Group G] [Finite G] : Prop :=
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
      D2TorusBorel p Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

theorem d2TorusMSide3_of (hX : D1NoXBlock3 G) (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime) : D2TorusMSide3 G := by
  intro hS hD1 M hM ha hb p _ hp hp5 P A H hMP hesc _ Rbar K hRbar hK hB
  exact hesc.pCore_ne_bot_of_torusBorel hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKin hKP hC3p hK5p
    (aglGlobal_of_setting hS) (d1For_of_setting hS) (noXBlockFor_of_setting hX hS) hp5 hRbar hK hB

theorem d2IndexCaseAt3_of_torusBorel {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (hiB : D2TorusBorelAt i Pp) (hp5 : ∀ p, Pp p → 5 ≤ p) (hMS : D2TorusMSide3 G)
    (hsurv : D2SurvivorsAll3 G) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hX : D1NoXBlock3 G) : D2IndexCaseAt3 G i Pp := by
  intro hSet hD1 M hM ha hb p hp hpc P A H R hMP hesc hmax Rbar K hRbar hK he
  have : Fact p.Prime := ⟨hesc.prime⟩
  have hB := hiB _ p hpc Rbar _ _ K hK he
  have hAR : A = R := hesc.A_eq_of_map_eq (hRbar.symm.trans hB.eq_A)
  subst hAR
  exact d2TheoremZ3_of hX h84 hCGT hSet hD1 M hM ha hb p hp P A H hMP hesc hmax
    (fun H' h' => hsurv hSet hD1 M hM ha hb p hp P A H' hMP h' hmax)
    (hMS hSet hD1 M hM ha hb p hp (hp5 p hpc) P A H hMP hesc hmax Rbar K hRbar hK hB)

end CFSG.LocalAnalysis.RankThreeTheoremC

module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIa
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbU3

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1SmallSPLZeroIbRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    IsSPLFamily p K → D1CzSP p z → D1CzOutside p z → d1MapPCore p M H = ⊥ →
    (p = 3 ∨ ¬ D1SmallIa p H K) → (p = 3 ∨ p = 5 ∨ IsSmallUnitary p K) → False

@[expose] def D1SmallSPLZeroIbRest2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    IsSPLFamily p K → D1CzSP p z → D1CzOutside p z → d1MapPCore p M H = ⊥ →
    (p = 3 ∨ ¬ D1SmallIa p H K) → (p = 3 ∨ (p = 5 ∧ ¬ IsSmallUnitary p K)) → False

theorem d1SmallSPLZeroNotIa_of_ibRest2 (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd)
    (hβo : KFactOutElemRank) (hKU2 : KFactUnitarySylowStructure) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hKF : KFactBlockCentCycIb)
    (hK2s : KFactAltSixSevenAutFive) (hK3 : CitedBlockTransvectionCyclic)
    (hK4 : CitedBlockAltNormalizerSq) (hG1 : StmtFaithfulExtraspecialRank)
    (h : D1SmallSPLZeroIbRest2) : D1SmallSPLZeroNotIa := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hspl hSP hout hV h3I
  by_cases h3 : p = 3
  · exact h G p P M H R Rbar K hd huniq z hz hspl hSP hout hV h3I (Or.inl h3)
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hnIa : ¬ D1SmallIa p H K := h3I.resolve_left h3
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 h3
  by_cases hU : IsSmallUnitary p K
  · exact hd.false_of_posZero_ib_unitary hK7 hK8 hβ hKO hΓ hSch hα hβo hKU2 h84 h85 h86 h93 hD2
      hK2 hC3' hK5' hKF hK2s hK3 hK4 hG1 hnIa hp5 hU hz hSP hout hV
  by_cases h5 : p = 5
  · exact h G p P M H R Rbar K hd huniq z hz hspl hSP hout hV h3I (Or.inr ⟨h5, hU⟩)
  have hp7 : 7 ≤ p := by
    rcases Nat.lt_or_ge p 7 with hlt | hge
    · exfalso
      have h6 : p = 6 := by omega
      exact hp2 ((hp.eq_one_or_self_of_dvd 2 (h6 ▸ (by norm_num : 2 ∣ 6))).resolve_left
        (by norm_num)).symm
    · exact hge
  have hL : IsSmallLinTwo p K := by
    rcases hspl with hl | hu | ⟨h3', -⟩
    · exact hl
    · exact absurd hu hU
    · exact absurd h3' h3
  exact hd.false_of_posZero_ib_linTwo hK7 hK8 hβ hKO hΓ hSch hα hβo h84 h85 h86 h93 hD2 hK2 hC3'
    hK5' (kFactBlockCentRankIb_of_cyc hKF) hK2s hK3 hK4 hnIa hp7 hL hz hSP hout hV

theorem d1SmallSPLZeroNotIa_of_ibRest2'
    (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd)
    (hβo' : KFactOutElemRankOdd) (hKU2 : KFactUnitarySylowStructure) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hKF : KFactBlockCentCycIb)
    (hK3 : CitedBlockTransvectionCyclic) (hK4 : CitedBlockAltNormalizerSq)
    (hG1 : StmtFaithfulExtraspecialRank) (h : D1SmallSPLZeroIbRest2) : D1SmallSPLZeroNotIa :=
  d1SmallSPLZeroNotIa_of_ibRest2 hK7 hK8 hβ hKO hΓ hSch hα (kFactOutElemRank_of_odd hβo') hKU2
    h84 h85 h86 h93 hD2 hK2 hC3' hK5' hKF kFactAltSixSevenAutFive hK3 hK4 hG1 h

end CFSG.AGLEmbedding

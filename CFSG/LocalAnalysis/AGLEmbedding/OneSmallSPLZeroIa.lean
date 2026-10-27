module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroPerf

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section IA

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_cz_ia (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (hOP : KFactBlockOutPrime) (hBO : KFactBlockOuterPerfectCent)
    (hd : D1OneSmallData p P M H R Rbar K) (hI : D1SmallIa p H K) (hp5 : 5 ≤ p)
    (hfam : IsSmallLinTwo p K ∨ IsSmallUnitary p K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hSP : D1CzSP p z) (hout : D1CzOutside p z) : False := by
  obtain ⟨T₁, hT₁, hF, hs, h3⟩ := hd.exists_oneLieFacts hK7 hK8 hp5 hfam
  obtain ⟨hzR, hzp, hzH, -⟩ := id hz
  have hzK : z ∈ H ⊓ M := ⟨hzH, hd.cfg.ext.le_M hzR⟩
  exact h3.false_of_perfect_centralizer hd.cfg.ind h84 h85 h86 h93 hD2 hKP hC3 hK5 hK2 hC3' hK5'
    hOP hBO hp5
    (fun U hU hUp => hd.coprime_card_of_perfect hI hT₁ hF.uPrime hF.outer_solvable hs hU hUp)
    hzK hzp fun D hDp hDz => hd.eq_bot_of_perfect_le_centralizer hβ hKO hΓ hSch hz hSP hout
      hzK.2 hDp hDz

end IA

@[expose] def D1SmallSPLZeroNotIa : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    IsSPLFamily p K → D1CzSP p z → D1CzOutside p z → d1MapPCore p M H = ⊥ →
    (p = 3 ∨ ¬ D1SmallIa p H K) → False

theorem d1SmallSPLZeroAll_of_notIa (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (hOP : KFactBlockOutPrime) (hBO : KFactBlockOuterPerfectCent) (h : D1SmallSPLZeroNotIa) :
    D1SmallSPLZeroAll := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hspl hSP hout hV
  by_cases h3 : p = 3
  · exact h G p P M H R Rbar K hd huniq z hz hspl hSP hout hV (Or.inl h3)
  by_cases hI : D1SmallIa p H K
  · have hp5 : 5 ≤ p := hd.cfg.red.prime.five_le_of_ne_two_of_ne_three hd.cfg.red.ne_two h3
    have hfam : IsSmallLinTwo p K ∨ IsSmallUnitary p K := by
      rcases hspl with hl | hu | ⟨h3', -⟩
      · exact Or.inl hl
      · exact Or.inr hu
      · exact absurd h3' h3
    exact hd.false_of_cz_ia hK7 hK8 hβ hKO hΓ hSch h84 h85 h86 h93 hD2 hKP hC3 hK5 hK2 hC3' hK5'
      hOP hBO hI hp5 hfam hz hSP hout
  · exact h G p P M H R Rbar K hd huniq z hz hspl hSP hout hV (Or.inr hI)

end CFSG.AGLEmbedding

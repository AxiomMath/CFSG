module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarTwoA
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3StarNF

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

@[expose] def D1CaseTwoNormalFormTwoA (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
      D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) →
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
        (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H →
      (p = 3 ∨ ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
        L ≤ d1X0 p M H) → False

theorem d1CaseTwoNormalForm_of_twoA {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (hInn : KFactBlockAutPrimeInner) (h : D1CaseTwoNormalFormTwoA G) : D1CaseTwoNormalForm G := by
  intro p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hK hNH
  by_cases hrest : p = 3 ∨ ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p),
      IsComponentOf L ⊤ ∧ L ≤ d1X0 p M H
  · exact h p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hK hNH hrest
  push Not at hrest
  obtain ⟨hp3, hall⟩ := hrest
  exact hd.toAt.false_of_nf_five (kFactCycAut_of_kFactOutCyclic hOut) hS hKL hSch h84 h85 h86 h93
    hD2 hKP hC3 hK5 hK2 hC3' hK5' hInn hz hNH hp3 hall
    fun _ => hd.cfg.pRank_inf_le_three Nat.prime_three (by decide)

end CFSG.LocalAnalysis.RankThreeTheoremC

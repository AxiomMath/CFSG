module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycRest
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3StarTwoA

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

@[expose] def D1CaseTwoNormalFormRest3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
      D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) →
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
        (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H →
      p = 3 → (∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ ∃ ζ ∈ barM M L,
          ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ ζ ^ 3 = 1 ∧
            ζ ≠ 1) → False

theorem d1CaseTwoNormalFormTwoA_of_rest3 {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hOP : KFactBlockOutPrime) (hK : CitedBlockToralThree)
    (hKA : CitedBlockToralThreeAut) (hTC : CitedBlockToralCycAut)
    (hTC3 : CitedBlockToralThreeCyc) (h3 : D1CaseTwoNormalFormRest3 G) :
    D1CaseTwoNormalFormTwoA G := fun p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hpX =>
  hd.toAt.false_of_nfTwoA (kFactCycAut_of_kFactOutCyclic hOut) hS hKL hInv.toIn hSch hSyl h84 h85
    h86 h93 hD2 hInn hKP hC3 hK5 hK2 hC3' hK5' hOP hK hKA hTC hTC3 hz hnSP hout hB0 hNH hpX
    (fun _ => hd.cfg.pRank_inf_le_three Nat.prime_three (by decide))
    (h3 p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH)

end CFSG.LocalAnalysis.RankThreeTheoremC

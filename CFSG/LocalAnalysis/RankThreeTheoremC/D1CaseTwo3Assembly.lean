module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Competitor
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Escape
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ZZFive

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseTwoEscaping (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥ →
      pCorePreimage p M ⊓ R ≠ ⊥ → False

theorem d1CaseTwoEscaping_of (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) :
    D1CaseTwoEscaping G :=
  fun _ _ _ _ _ _ hd _ hL hLX₀ hVL hV => hd.false_of_escape hOut hS hKL h84 hD2 hL hLX₀ hVL hV

@[expose] def D1CaseTwoRankThree (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar → False

theorem d1CaseTwoRankThree_of_unique (hOut : KFactOutCyclic) (hC : D1CaseTwoComp3 G)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G)
    (hSch : KFactCatalogSchreier) (hU : D1CaseTwoUnique G) : D1CaseTwoRankThree G := by
  intro p P M H R Rbar hd
  obtain ⟨H₀, Rbar₀, hd₀, huniq⟩ := exists_unique_layer_of
    (Dat := fun H Rb => D1CaseTwoData3 p P M H R Rb) (fun _ _ hd => hd.toAt)
    (fun _ _ hd _ hH' hJH' hRH' => hd.competitor hOut hC hS hInv hSch hH' hJH' hRH')
    (kFactCycAut_of_kFactOutCyclic hOut) hS hKL hd
  exact hU p P M H₀ R Rbar₀ hd₀ huniq

theorem d1CaseTwoUnique_of (hOut : KFactOutCyclic) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock)
    (h0 : D1CaseTwoPosZero G) (h2a : D1CaseTwoPosNTwoA G) (hzz : D1CaseTwoZZ G)
    (hesc : D1CaseTwoEscaping G) : D1CaseTwoUnique G := fun p P M H R Rbar hd huniq =>
  hd.toAt.false_of_unique (kFactCycAut_of_kFactOutCyclic hOut) hS hKL h84 hD2 hCGT huniq
    (h0 p P M H R Rbar hd huniq) (hesc p P M H R Rbar hd) (h2a p P M H R Rbar hd huniq)
    (hzz p P M H R Rbar hd huniq)

theorem d1CaseTwoRankThree_of (hOut : KFactOutCyclic) (hC : D1CaseTwoComp3 G)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (h0 : D1CaseTwoPosZero G) (h2a : D1CaseTwoPosNTwoA G) (hz3 : D1CaseTwoZZThree G) :
    D1CaseTwoRankThree G :=
  d1CaseTwoRankThree_of_unique hOut hC hS hKL hInv hSch
    (d1CaseTwoUnique_of hOut hS hKL h84 hD2 hCGT h0 h2a
      (d1CaseTwoZZ_of_zzThree hOut hS hKL hSch h84 h85 h86 h93 hD2 hKin hKP hC3 hK5 hz3)
      (d1CaseTwoEscaping_of hOut hS hKL h84 hD2))

end CFSG.LocalAnalysis.RankThreeTheoremC

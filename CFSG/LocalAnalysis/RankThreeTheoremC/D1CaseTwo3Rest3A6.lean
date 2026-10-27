module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Rest3b
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NotThreeASix
import CFSG.LocalAnalysis.RankThreeTheoremC.D1SL3InvertCentre

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseTwoRest3A6 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
      D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) →
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
        (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H →
      p = 3 → (∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ ∃ ζ ∈ barM M L,
          ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ ζ ^ 3 = 1 ∧
            ζ ≠ 1) →
      (∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧
        Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))) →
      False

theorem d1CaseTwoRest3_of_rest3A6 (hk : D1CaseTwoKFacts3 G)
    (hZ : KFactFixCensusCenter) (h : D1CaseTwoRest3A6 G) : D1CaseTwoRest3 G := by
  intro p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW
  by_cases h6 : ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧
      Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))
  · exact h p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW h6
  subst hp3
  obtain ⟨L, hL, ζ, hζA, hζC, hζ3, hζ1⟩ := hW
  exact D1CaseTwoData3.false_of_center_not_threeASix hk.out hk.seitzCyc hk.caseTwoLocal hk.inv
    hk.schreier hk.sylow hk.eightFour hk.eightFive hk.eightSix hk.nineThree hk.noXBlock
    hk.toralThree hZ sl3InvertCentre_holds hd hz hnSP hout hB0 hNH
    (fun L' hL' hZ hA6 => h6 ⟨L', hL', hZ, hA6⟩) hL hζA hζC hζ3 hζ1

theorem d1CaseTwoRest3b_of_rest3A6 (hk : D1CaseTwoKFacts3 G)
    (hZ : KFactFixCensusCenter) (h : D1CaseTwoRest3A6 G) : D1CaseTwoRest3b G :=
  d1CaseTwoRest3b_of_rest3 (d1CaseTwoRest3_of_rest3A6 hk hZ h)

theorem d1CaseTwoRest3A6_of_rest3b (h : D1CaseTwoRest3b G) : D1CaseTwoRest3A6 G :=
  fun p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW h6 =>
    h p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW (Or.inl h6)

end CFSG.LocalAnalysis.RankThreeTheoremC

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ToralCenterRest7

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure D1CaseTwoRest3Facts : Prop where
  toralThreeCenter : CitedBlockToralThreeCenter
  l28AutThree : KFactL28AutThree

@[expose] def D1CaseTwoRest3b (G : Type) [Group G] [Finite G] : Prop :=
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
      ((∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧
          Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
          Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))) ∨
        ∃ y ∈ R, y ^ 3 = (z : G)) → False

theorem d1CaseTwoRest3_of_rest3b (hk : D1CaseTwoKFacts3 G) (hF : D1CaseTwoRest3Facts)
    (h : D1CaseTwoRest3b G) : D1CaseTwoRest3 G := by
  intro p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW
  by_cases h6 : ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧
      Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))
  · exact h p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW (Or.inl h6)
  by_cases hc : ∃ y ∈ R, y ^ 3 = (z : G)
  · exact h p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW (Or.inr hc)
  subst hp3
  obtain ⟨L, hL, ζ, hζA, hζC, hζ3, hζ1⟩ := hW
  exact D1CaseTwoData3.false_of_center_small hk.out hk.seitzCyc hk.caseTwoLocal hk.inv
    hk.schreier hk.sylow hk.eightFour hk.eightFive hk.eightSix hk.nineThree hk.noXBlock
    hk.toralThree hF.l28AutThree hF.toralThreeCenter hd hz hnSP hout hB0 hKax hNH
    (fun L' hL' hZ hA6 => h6 ⟨L', hL', hZ, hA6⟩) hL hζA hζC hζ3 hζ1 hc

theorem d1CaseTwo3_of_residues3b (hk : D1CaseTwoKFacts3 G) (hF : D1CaseTwoRest3Facts)
    (hC : D1CaseTwoComp3 G) (hrest : D1CaseTwoRest3b G) : D1CaseTwo3 G :=
  d1CaseTwo3_of_residues3 hk hC (d1CaseTwoRest3_of_rest3b hk hF hrest)

theorem d1CaseTwoRest3b_of_rest3 (h : D1CaseTwoRest3 G) : D1CaseTwoRest3b G :=
  fun p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW _ =>
    h p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW

end CFSG.LocalAnalysis.RankThreeTheoremC

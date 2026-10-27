module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexRest
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem D1CaseTwoData3.nf_inputs (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) {P : Sylow 3 G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} (hd : D1CaseTwoData3 3 P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand 3 M H R z) (hnSP : ¬ D1CzSP 3 (z : G))
    (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H) :
    D1PhaseThree 3 P M H R ∧ ∃ hzM : (z : G) ∈ M, (z : G) ∈ (P : Subgroup G) ∧
      (z : G) ^ 3 = 1 ∧ Subgroup.centralizer ({(z : G)} : Set G) ≤ H ∧
      (∀ E : Subgroup G, E ≤ Subgroup.centralizer ({(z : G)} : Set G) →
        IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3) ∧
      (∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
        ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q) ∧
      (∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(z : G), hzM⟩ ∈
          barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :=
  D1CaseTwoDataAt.nf_inputs (hAut := (kFactCycAut_of_kFactOutCyclic hOut)) (hS := hS) (hKL := hKL)
    (hInv := hInv.toIn) (hSch := hSch) (hSyl := hSyl) (h84 := h84) (h85 := h85) (h86 := h86)
    (h93 := h93) (hD2 := hD2) (hK := hK) (hd := hd.toAt) (hz := hz) (hnSP := hnSP) (hout := hout)
    (hB0 := hB0) (hNH := hNH)

end CFSG.LocalAnalysis.RankThreeTheoremC

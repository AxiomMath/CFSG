module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterRest7
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem D1CaseTwoData3.false_of_center_small (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) (h28 : KFactL28AutThree) (hBF : CitedBlockToralThreeCenter)
    {P : Sylow 3 G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hd : D1CaseTwoData3 3 P M H R Rbar) {z : H} (hz : D1CaseTwoCand 3 M H R z)
    (hnSP : ¬ D1CzSP 3 (z : G)) (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hKax : D1CaseTwoKAxis 3 P M R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H)
    (hno6 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      Nat.card (Subgroup.center ↥(barM M L)) = 3 →
      ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {ζ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hζA : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (hcube : ¬ ∃ y ∈ R, y ^ 3 = (z : G)) : False :=
  D1CaseTwoDataAt.false_of_center_small (hAut := (kFactCycAut_of_kFactOutCyclic hOut)) (hS := hS)
    (hKL := hKL) (hInv := hInv.toIn) (hSch := hSch) (hSyl := hSyl) (h84 := h84) (h85 := h85)
    (h86 := h86) (h93 := h93) (hD2 := hD2) (hK := hK) (h28 := h28) (hBF := hBF) (hd := hd.toAt)
    (hz := hz) (hnSP := hnSP) (hout := hout) (hB0 := hB0) (hKax := hKax) (hNH := hNH) (hno6 := hno6)
    (hL := hL) (hζA := hζA) (hζC := hζC) (hζ3 := hζ3) (hζ1 := hζ1) (hcube := hcube)

end CFSG.LocalAnalysis.RankThreeTheoremC

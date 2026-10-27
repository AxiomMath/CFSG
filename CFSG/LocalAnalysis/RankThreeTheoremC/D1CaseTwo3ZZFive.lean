module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoZZFive
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.false_of_zz_prime (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hd : D1CaseTwoData3 p P M H R Rbar) (hp5 : 5 ≤ p)
    {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₁ : IsComponentOf L₁ ⊤)
    (huL : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥)
    (hA : d1MapPCore p M H ⊓ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥)
    {z : H} (hzp : orderOf z = p)
    (hzO : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      CFSG.pCore p (H ⧸ primeComplementCore (G := H) p))
    (hzS : (z : G) ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆) : False :=
  D1CaseTwoDataAt.false_of_zz_prime (hAut := (kFactCycAut_of_kFactOutCyclic hOut)) (hS := hS)
    (hKL := hKL) (hSch := hSch) (h84 := h84) (h85 := h85) (h86 := h86) (h93 := h93) (hD2 := hD2)
    (hKin := hKin) (hKP := hKP) (hC3 := hC3) (hK5 := hK5) (hd := hd.toAt) (hp5 := hp5) (hL₁ := hL₁)
    (huL := huL) (hmeet := hmeet) (hA := hA) (hzp := hzp) (hzO := hzO) (hzS := hzS)

end Data

theorem d1CaseTwoZZ_of_zzThree {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hKin : KFactTwoGenInner)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hz3 : D1CaseTwoZZThree G) : D1CaseTwoZZ G := by
  intro p P M H R Rbar hd huniq L₁ hL₁ huL hmeet hA hW z hzR hzp hzO hzS
  by_cases hp3 : p = 3
  · subst hp3
    exact hz3 P M H R Rbar hd huniq L₁ hL₁ huL hmeet hA hW z hzR hzp hzO hzS
  · exact hd.false_of_zz_prime hOut hS hKL hSch h84 h85 h86 h93 hD2 hKin hKP hC3 hK5
      (hd.cfg.red.prime.five_le_of_ne_two_of_ne_three hd.cfg.red.ne_two hp3) hL₁ huL hmeet hA hzp hzO
      hzS

end CFSG.LocalAnalysis.RankThreeTheoremC

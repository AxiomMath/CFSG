module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZN
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockClose
import CFSG.LocalAnalysis.AGLEmbedding.OneLiePerfect

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section ZZ

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.not_mem_pCorePreimage (hd : D1OneLieData p P M H R Rbar K)
    (hWK : d1MapPCore p M H ≤ K) {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K)
    (hzp : orderOf z = p) : z ∉ pCorePreimage p M :=
  hd.toCore.not_mem_pCorePreimage hWK hzR hzN hzp

private theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    5 ≤ p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  omega

theorem D1OneLieData.mem_nclIn_twoCore (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) {z : G}
    (hzJ : z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆) :
    z ∈ nclIn M (pCoreOf 2 H) := by
  have h3 := hd.toPhaseThree hK
  have hSM : pCoreOf 2 H ≤ M := h3.twoCore_le
  exact nclIn_le ((hd.commutator_nclIn_le hK h84 hD2 hY).trans (le_nclIn hSM))
    (nclIn_le_self M _) (le_normalizer_nclIn M _) hzJ

end ZZ

theorem d1OneLieZZaCore_of (hK : KFactOneLie) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hKin : KFactTwoGenInner)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hΓ : KFactOneLieBorelSolvable) (h3 : D1OneLieZZ3) :
    D1OneLieZZaCore := by
  intro G _ _ p P M H R Rbar K hd huniq hY hI hWK hU hno z hzR hzN hzp hzJ
  have hp := hd.cfg.red.prime
  by_cases hp3 : p = 3
  · exact h3 G p P M H R Rbar K hd huniq hY hI hWK hU hno hp3 z hzR hzN hzp hzJ
  have hp5 := five_le_of_prime hp hd.cfg.red.ne_two hp3
  have h3' := hd.toPhaseThree hK
  have hzS : z ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 H (hd.cfg.ext.le_H hzR)
  have hzq : z ^ p ^ 1 = 1 := by rw [pow_one, ← hzp]; exact pow_orderOf_eq_one z
  obtain ⟨L, hL, -, V, hV, hVp, hpV⟩ := h3'.exists_component_of_not_mem h84 h85 h86 h93 hD2 hKin
    hKP hC3 hK5 hp5 (hd.mem_nclIn_twoCore hK h84 hD2 hY hzJ) hzS hzq
    (hd.not_mem_pCorePreimage hWK hzR hzN hzp)
  have hLK : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ H ⊓ M := by
    rw [h3'.normalizer_twoCore_H]
    exact inf_le_inf_left H hL.le
  have hcop := coprime_card_of_le_barM_of_perfect inf_le_right
    (fun U hU hUp => hd.coprime_card_of_perfect hK hΓ hI hU hUp) (hV.trans (barM_mono hLK)) hVp
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop hpV

theorem d1OneLieZZbCore_of (hK : KFactOneLie) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hKin : KFactTwoGenInner)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (h3 : D1OneLieZZb3) (hb : D1OneLieZZbHat) :
    D1OneLieZZbCore := by
  intro G _ _ p P M H R Rbar K hd huniq hY hI hWK hU hno z hzR hzN hzp hzJ
  have hp := hd.cfg.red.prime
  by_cases hp3 : p = 3
  · exact h3 G p P M H R Rbar K hd huniq hY hI hWK hU hno hp3 z hzR hzN hzp hzJ
  have hp5 := five_le_of_prime hp hd.cfg.red.ne_two hp3
  have h3' := hd.toPhaseThree hK
  have hzS : z ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 H (hd.cfg.ext.le_H hzR)
  have hzq : z ^ p ^ 1 = 1 := by rw [pow_one, ← hzp]; exact pow_orderOf_eq_one z
  obtain ⟨L, hL, hmove, V, hV, hVp, hpV⟩ := h3'.exists_component_of_not_mem h84 h85 h86 h93 hD2
    hKin hKP hC3 hK5 hp5 (hd.mem_nclIn_twoCore hK h84 hD2 hY hzJ) hzS hzq
    (hd.not_mem_pCorePreimage hWK hzR hzN hzp)
  exact hmove (hb G p P M H R Rbar K hd huniq hY hI hWK hU hno hp5 z hzR hzN hzp hzJ L hL
    ⟨V, hV, hVp, hpV⟩)

end CFSG.AGLEmbedding

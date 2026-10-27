module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormal
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVEven
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCover
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbUnique
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarRes
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.ibCore_of_ibNormal (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hK8 : KFactSmallBorelSolvable) (hΓs : KFactSmallGammaSolvableSpor)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hB : D1IbBlockInputs) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hnIa : ¬ D1SmallIa p H K) (hB0 : D1CzB0 p R z)
    (hL : ¬ (p = 3 ∧ IsLinThreeFour K))
    (hVH : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H)
    (hp5 : 5 ≤ p) (hA : ¬ IsAltTwoP p K) (hFi : ¬ (p = 5 ∧ IsFi22 K)) :
    D1IbCore p P M H R Rbar K z := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := centralizer_le_of_normalizer_vz_le hVH
  have hLa : D1SmallLa p M H Rbar K := d1SmallLa_of_not hL
  obtain ⟨hcardR, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 hLa
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzp1 : z ^ p = 1 := by rw [← hz.2.1]; exact pow_orderOf_eq_one z
  have hexpR : ∀ r ∈ R, r ^ p = 1 := by
    intro r hr
    obtain ⟨t, ht, i, rfl⟩ := hdec r hr
    have hc : Commute t (z ^ i) := Commute.pow_right
      (show Commute t z from Subgroup.mem_centralizer_singleton_iff.mp
        (hRC (d1LiftX_le p H R K ht))) i
    rw [hc.mul_pow, hd.pow_eq_one_of_mem_d1LiftX hExp ht, ← pow_mul, mul_comm, pow_mul, hzp1,
      one_pow, one_mul]
  have hph := hd.toPhaseThree hUP hL hFi
  obtain ⟨T₁, hT₁, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hUPK := hUP K hs hn hc p hp hp2 T₁ hTnc hΓT hd.small hL hFi
  have hout := hSch K hs hn hc
  have hsolv : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)) := by
    by_cases hfam : IsSmallLinTwo p K ∨ IsSmallUnitary p K
    · exact hK8 K p hp hp5 hfam T₁
    · push Not at hfam
      exact hΓs K hs hn hc p hp hp2 T₁ hTnc hΓT hd.small hfam.1 hfam.2 hA hL hFi
  have hperf := D1OneSmallData.perf_barM hd hph hT₁ hUPK hout hsolv hcardR
  have hzM : z ∈ M := hph.le_M hz.1
  have huniq := D1PhaseThree.barM_eq_of_perf hph hd.cfg.ind hB.h84 hB.h85 hB.h86 hB.h93 hB.hD2
    hInn hKP hC3p hK5p hB.hK2 hB.hC3 hB.hK5 hp5 ⟨hz.2.2.1, hzM⟩ hz.2.1 hCz hperf
  have hcov := D1OneSmallData.exists_perfect_cover hd hz hzM hnIa hcardR
  exact ⟨hd, hz, hB0, hCz, hp5, hFi, hph, hdec, hexpR, hperf, huniq, hcov⟩

end CFSG.AGLEmbedding

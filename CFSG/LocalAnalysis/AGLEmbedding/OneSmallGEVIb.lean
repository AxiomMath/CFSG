module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormal
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBlock
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCoreNormal
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbToral
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbOuter

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1IbConfig.false {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}
    (hc : D1IbConfig p P M H R Rbar K z) (hB : D1IbBlockInputs)
    (hOrb : KFactSmallOrbits) : False := by
  obtain ⟨L, hL⟩ := hc.phase.exists_weakSBlock hB.h84 hB.hD2
  have hRM := hc.phase.le_M
  obtain ⟨h1, h2⟩ := hc.inv_subgroup hOrb inf_le_left (hc.rPart_inv hL le_rfl)
  obtain ⟨h3, h4⟩ := hc.inv_subgroup hOrb inf_le_left
    (hc.rPart_inv hL (normalizer_le_normalizer_centralizer _))
  have hzC : z ∉ rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :=
    fun h => hc.zbar_not_mem_centralizer hL ((mem_rPart hRM hc.elt.1).mp h)
  by_cases hzB : z ∈ rPart M R (barM M L)
  · have hzbL := (mem_rPart hRM hc.elt.1).mp hzB
    rcases h1 with hT | hT
    · refine hc.false_of_le_rPart hB hL fun r hr => ?_
      obtain ⟨t, ht, i, rfl⟩ := hc.dec r hr
      exact Subgroup.mul_mem _ (hT ht) (Subgroup.pow_mem _ hzB i)
    · have hBz := (h2 hT).1
      rcases h3 with hTC | hTC
      · exact hc.false_of_d1LiftX_le_C hOrb hL hBz hzbL hTC
      · exact hc.false_of_rPart_C_eq_bot hB hL hBz hzbL ((h4 hTC).2 hzC)
  · rcases h1 with hT | hT
    · exact hc.false_of_d1LiftX_le_of_not_mem hB hOrb hL hT hzB
    · exact hc.false_of_rPart_block_eq_bot hB hL ((h2 hT).2 hzB)

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_ibNormal (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hK8 : KFactSmallBorelSolvable) (hΓs : KFactSmallGammaSolvableSpor)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hB : D1IbBlockInputs) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hnIa : ¬ D1SmallIa p H K) (hB0 : D1CzB0 p R z)
    (hL : ¬ (p = 3 ∧ IsLinThreeFour K))
    (hVH : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H)
    (hp5 : 5 ≤ p)
    (hT2 : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 2)
    (hA : ¬ IsAltTwoP p K) (hFi : ¬ (p = 5 ∧ IsFi22 K)) : False := by
  exact ((hd.ibCore_of_ibNormal hUP hSch hK8 hΓs hOut hExp hInn hKP hC3p hK5p hB hz hnIa hB0 hL
    hVH hp5 hA hFi).toIbConfig hT2).false hB hOrb

end CFSG.AGLEmbedding

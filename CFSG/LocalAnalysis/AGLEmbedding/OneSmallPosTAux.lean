module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZNAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section ZN

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_not_mem_normal (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hCW : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    {C' : Subgroup G} (hMC' : M ≤ Subgroup.normalizer (C' : Set G))
    (hNJC' : ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ ≤ C')
    {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p) (hzC' : z ∉ C') :
    False :=
  hd.toCore.false_of_not_mem_normal h3 h84 hCGT hD2 huniq hY hCW hMC' hNJC' hzR hzN hzp hzC'

theorem D1OneSmallData.mem_nclIn_commutator (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hCW : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p) :
    z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ := by
  by_contra hz
  exact hd.false_of_not_mem_normal h3 h84 hCGT hD2 huniq hY hCW (le_normalizer_nclIn M _)
    (le_nclIn ((hd.commutator_nclIn_le h3 h84 hD2 hY).trans h3.twoCore_le)) hzR hzN hzp hz

theorem D1OneSmallData.not_mem_pCorePreimage (hd : D1OneSmallData p P M H R Rbar K)
    (hWK : d1MapPCore p M H ≤ K) {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K)
    (hzp : orderOf z = p) : z ∉ pCorePreimage p M :=
  hd.toCore.not_mem_pCorePreimage hWK hzR hzN hzp

theorem D1OneSmallData.mem_nclIn_twoCore (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) {z : G}
    (hzJ : z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆) :
    z ∈ nclIn M (pCoreOf 2 H) :=
  nclIn_le ((hd.commutator_nclIn_le h3 h84 hD2 hY).trans (le_nclIn h3.twoCore_le))
    (nclIn_le_self M _) (le_normalizer_nclIn M _) hzJ

end ZN

end CFSG.AGLEmbedding

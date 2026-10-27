module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Criterion
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

variable {G : Type} [Group G] {L : Subgroup G}

theorem relIndex_normalizer_dvd (hL : commutator L = ⊤) :
    (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) ∣
      (innAut (L ⧸ center L)).index := by
  have hsub : (L ⊔ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) =
      (innAut (L ⧸ center L)).comap (normalizerAction L) := by
    ext g
    exact (normalizerAction_mem_range_conj_iff hL g).symm
  have hnorm : (innAut (L ⧸ center L)).Normal := normal_range_conj (L ⧸ center L)
  rw [Subgroup.relIndex, hsub, Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

end CFSG.EvenSporadicStandard.Fin76b

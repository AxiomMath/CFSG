module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal
import CFSG.GroupTheory.CoprimeSupPCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_inf_centralizer_sup_pCoreOf_two {K W N : Subgroup G}
    (hWK : W ≤ normalizer (K : Set G)) (hW : IsPGroup 3 W) (hNK : N ≤ K)
    (hperf : ⁅K, K⁆ = K) (hKW : ⁅W, K⁆ ≤ N) (hN : ⁅K, N⁆ ≤ pCoreOf 2 K) :
    K = (K ⊓ centralizer (W : Set G)) ⊔ pCoreOf 2 K := by
  set O : Subgroup G := pCoreOf 2 K with hO
  have hKO : K ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 K
  have hWO : W ≤ Subgroup.normalizer (O : Set G) :=
    hWK.trans (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_normalizer_characteristic
      (CFSG.pCore 2 K) (CFSG.pCore_characteristic (p := 2)))
  have hOO : O ≤ K ⊔ W :=
    (Subgroup.map_subtype_le (CFSG.pCore 2 K)).trans le_sup_left
  have hrot : ⁅⁅K, K⁆, W⁆ ≤ O := by
    refine CFSG.GroupTheory.commutator_commutator_le_of_rotate_normal
      (M := K ⊔ W) (A := K) (B := W) (N := O) le_sup_left le_sup_right hOO
      (sup_le hKO hWO) ?_ ?_
    · calc ⁅⁅K, W⁆, K⁆ = ⁅⁅W, K⁆, K⁆ := by rw [Subgroup.commutator_comm K W]
        _ ≤ ⁅N, K⁆ := Subgroup.commutator_mono hKW le_rfl
        _ = ⁅K, N⁆ := Subgroup.commutator_comm N K
        _ ≤ O := hN
    · calc ⁅⁅W, K⁆, K⁆ ≤ ⁅N, K⁆ := Subgroup.commutator_mono hKW le_rfl
        _ = ⁅K, N⁆ := Subgroup.commutator_comm N K
        _ ≤ O := hN
  have hKWle : ⁅K, W⁆ ≤ O := by
    have h := hrot
    rwa [hperf] at h
  have hWKle : ⁅W, K⁆ ≤ O := by
    rwa [Subgroup.commutator_comm K W] at hKWle
  have h := CFSG.GroupTheory.inf_centralizer_sup_pCoreOf_eq_of_commutator_le
    (L := K) (A := W) (r := 3) (by norm_num) (by norm_num) hW hWKle
  simpa only [hO] using h.symm

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end

module

public import CFSG.LocalAnalysis.EvenBN.U4.RootD2

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (centralizerMod mem_normalizer_inf
  exists_mem_forall_conj_mem_of_isPGroup)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem normalizer_H_inf_C_le_normalizer_D2 (hS : Setting h L η t Q T) {c : G}
    (hc : c ∈ normalizer (CFSG.centerIn Q : Set G)) :
    c ∈ normalizer (miyamotoD2G h L η t Q : Set G) := by
  rw [hS.miyamotoD2G_eq]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.le_normalizer_oTwo _ (hS.H_le_normalizer_M hc)

theorem t_mem_D2 (hS : Setting h L η t Q T) : t ∈ miyamotoD2G h L η t Q :=
  hS.EB2_le_D2 (mem_sup_right (mem_sup_left (mem_zpowers t)))

theorem A2_le_D2 (hS : Setting h L η t Q T) : miyamotoA2G h L η ≤ miyamotoD2G h L η t Q :=
  (le_sup_right.trans le_sup_right).trans hS.EB2_le_D2

end Setting

end CFSG.LocalAnalysis.EvenBN.U4

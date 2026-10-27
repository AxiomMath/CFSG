module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

namespace NineEightCondA

section Helpers

variable {X : Type*} [Group X]

theorem mem_normalizer_sSup {S : Set (Subgroup X)} {n : X}
    (h : ∀ Y ∈ S, n ∈ Subgroup.normalizer (Y : Set X)) :
    n ∈ Subgroup.normalizer ((sSup S : Subgroup X) : Set X) := by
  rw [sSup_eq_iSup']
  exact Subgroup.iInf_normalizer_le_normalizer_iSup _ (Subgroup.mem_iInf.mpr fun Y => h Y Y.2)

end Helpers

variable {p : ℕ} {M H : Subgroup G}

theorem kSub_eq_sSup (hJ : ¬ AGL81C.pLayerIn p H ≤ M) :
    AGL81C.kSub p M H = sSup {Y : Subgroup G | AGL81C.IsPComponentIn p Y H ∧ ¬ Y ≤ M} := by
  unfold AGL81C.kSub
  rw [if_neg hJ]

theorem kSub_le (hJ : ¬ AGL81C.pLayerIn p H ≤ M) : AGL81C.kSub p M H ≤ H := by
  rw [kSub_eq_sSup hJ]
  exact sSup_le fun Y hY => hY.1.1

theorem primeComplementCore_le_normalizer_kSub [Fact p.Prime] (hJ : ¬ AGL81C.pLayerIn p H ≤ M) :
    primeComplementCore (G := H) p ≤
      Subgroup.normalizer (((AGL81C.kSub p M H).subgroupOf H : Subgroup H) : Set H) := by
  intro n hn
  have h1 : (n : G) ∈ Subgroup.normalizer ((AGL81C.kSub p M H : Subgroup G) : Set G) := by
    rw [kSub_eq_sSup hJ]
    refine mem_normalizer_sSup fun Y hY => ?_
    have h2 : n ∈ Subgroup.normalizer ((Y.subgroupOf H : Subgroup H) : Set H) :=
      CFSG.ComponentClassification.UnbalancedLayer.pPrimeCore_le_normalizer hY.1.2 hn
    rw [← Subgroup.subgroupOf_normalizer_eq hY.1.1] at h2
    exact h2
  rw [← Subgroup.subgroupOf_normalizer_eq (kSub_le hJ)]
  exact h1

end NineEightCondA

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

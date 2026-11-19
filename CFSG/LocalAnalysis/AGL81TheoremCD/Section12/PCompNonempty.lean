module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightCondA

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_pComponentIn_not_le_of_not_pLayerIn_le {p : ℕ} [Fact p.Prime]
    {M H : Subgroup G} (hJ : ¬ pLayerIn p H ≤ M) :
    ∃ Y : Subgroup G, IsPComponentIn p Y H ∧ ¬ Y ≤ M := by
  by_contra h
  push Not at h
  apply hJ
  rw [pLayerIn]
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  refine sSup_le fun L hL => ?_
  have hcomp : IsPComponentIn p (L.map H.subtype) H := by
    refine ⟨Subgroup.map_subtype_le L, ?_⟩
    have hsub : (L.map H.subtype).subgroupOf H = L := by
      ext x
      simp
    rw [hsub]
    exact hL
  have hLM : L.map H.subtype ≤ M := h _ hcomp
  exact Subgroup.map_le_iff_le_comap.mp hLM

omit [Finite G] in
theorem not_kSub_le_M_of_not_pLayerIn_le {p : ℕ} [Fact p.Prime] {M H : Subgroup G}
    (hJ : ¬ pLayerIn p H ≤ M) : ¬ kSub p M H ≤ M := by
  intro hKM
  obtain ⟨Y, hY, hYM⟩ := exists_pComponentIn_not_le_of_not_pLayerIn_le hJ
  have hYk : Y ≤ kSub p M H := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightCondA.kSub_eq_sSup hJ]
    exact le_sSup (s := {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M}) ⟨hY, hYM⟩
  have hYM' : Y ≤ M := fun y hy => hKM (hYk hy)
  exact hYM hYM'

omit [Finite G] in
theorem not_kSub_le_M_of_le {p : ℕ} [Fact p.Prime] {M H : Subgroup G}
    (hgen : H ≤ kSub p M H ⊔ (H ⊓ M)) (hH : ¬ H ≤ M) : ¬ kSub p M H ≤ M := by
  intro hKM
  exact hH (hgen.trans (sup_le hKM inf_le_right))

omit [Finite G] in
theorem not_kSub_le_M_of_pLayerIn_le {p : ℕ} [Fact p.Prime] {M H : Subgroup G}
    (hH : ¬ H ≤ M) (hgen : pLayerIn p H ≤ M → H ≤ kSub p M H ⊔ (H ⊓ M)) :
    ¬ kSub p M H ≤ M := by
  by_cases hle : pLayerIn p H ≤ M
  · exact not_kSub_le_M_of_le (hgen hle) hH
  · exact not_kSub_le_M_of_not_pLayerIn_le hle

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

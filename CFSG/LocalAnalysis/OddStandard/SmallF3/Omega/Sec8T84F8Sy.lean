module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5L4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section TData

variable {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84_exists_c (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2)
    (hrk : ∀ R : Subgroup G, R ≤ centralizer ({t} : Set G) → ¬ IsElemAb2 R 8)
    (hT : IsSylow2Of T (normalizer (E : Set G))) (hTS : ¬ IsSylow2Of T ⊤) :
    ∃ c : G, c ∈ centralizer ({t} : Set G) ∧ c ∈ normalizer (T : Set G) ∧ c ∉ T ∧
      IsPGroup 2 ↥((T ⊓ centralizer ({t} : Set G)) ⊔ zpowers c) := by
  obtain ⟨P, hPsyl, hTP⟩ := exists_isSylow2Of_ge (H := ⊤) hT.2.1 le_top
  have hTPne : T ≠ P := by
    intro h
    apply hTS
    rw [h]
    exact hPsyl
  have hHne : T.subgroupOf P ≠ ⊤ := by
    intro h
    exact hTPne (le_antisymm hTP (Subgroup.subgroupOf_eq_top.mp h))
  have hHlt : T.subgroupOf P < ⊤ := lt_top_iff_ne_top.mpr hHne
  haveI : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hPsyl.2.1
  have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent
  have hlt : T.subgroupOf P < normalizer (T.subgroupOf P) := hnc (T.subgroupOf P) hHlt
  obtain ⟨n, hn_norm, hn_notT⟩ := SetLike.exists_of_lt hlt
  have hsub : n ∈ (normalizer (T : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hTP]
    exact hn_norm
  have hnN : (n : G) ∈ normalizer (T : Set G) := Subgroup.mem_subgroupOf.mp hsub
  have hnT : (n : G) ∉ T := fun h => hn_notT (Subgroup.mem_subgroupOf.mpr h)
  obtain ⟨a, ha, hc⟩ := sec8t84_normalizer_decomp D hrk (n : G) hnN
  have hT1T : T1 ≤ T := by
    intro x hx
    rw [D.T_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_left hx)
  have haT : a ∈ T := hT1T ha
  have haP : a ∈ P := hTP haT
  have hnP : (n : G) ∈ P := n.2
  refine ⟨a⁻¹ * (n : G), hc, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (le_normalizer haT)) hnN
  · intro hmem
    apply hnT
    have hac : a * (a⁻¹ * (n : G)) = (n : G) := by group
    rw [← hac]
    exact Subgroup.mul_mem _ haT hmem
  · apply hPsyl.2.1.to_le
    apply sup_le
    · exact inf_le_left.trans hTP
    · exact Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.inv_mem _ haP) hnP)

end TData

end CFSG.OddStandard.SmallF3.Omega

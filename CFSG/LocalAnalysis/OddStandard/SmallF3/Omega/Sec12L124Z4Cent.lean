module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec124_cent_le_K [Finite G] {C S N K : Subgroup G}
    (hout : K.relIndex N ≤ 2) (hCN : C ≤ N) (hS : IsSylow2Of S C) (hSK : S ≤ K) : C ≤ K := by
  have hne : K.relIndex N ≠ 0 := by
    show (K.subgroupOf N).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have h1 : K.relIndex C ≤ 2 := (Subgroup.relIndex_le_of_le_right hCN hne).trans hout
  have h2 : K.relIndex C ∣ S.relIndex C := by
    have hSKC : S ≤ K ⊓ C := le_inf hSK hS.1
    have h := Subgroup.relIndex_dvd_of_le_left C hSKC
    rwa [Subgroup.inf_relIndex_right] at h
  have h3 : ¬ 2 ∣ S.relIndex C := hS.2.2
  have h4 : K.relIndex C = 1 := by
    interval_cases hk : K.relIndex C
    · exact absurd (by rw [zero_dvd_iff.mp h2]; exact dvd_zero 2) h3
    · rfl
    · exact absurd (hk ▸ h2) h3
  exact Subgroup.relIndex_eq_one.mp h4

end CFSG.OddStandard.SmallF3.Omega

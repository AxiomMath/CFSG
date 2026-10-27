module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F5

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

abbrev U81 (h : Hyp59 H) (v : H) : Subgroup H := h.S ⊔ zpowers v

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

structure IsV (v : H) : Prop where
  mem_N : v ∈ normalizer (h.S : Set H)
  conj_a : v⁻¹ * h.a * v = d.z
  conj_z : v⁻¹ * d.z * v = h.a
  sq_mem : v * v ∈ h.S
  isPGroup : IsPGroup 2 (zpowers v)

variable {d} {v : H} (hv : d.IsV v)
include hv

theorem isPGroup_U : IsPGroup 2 (h.U81 v) :=
  IsPGroup.to_sup_of_normal_left' h.toHyp52.isPGroup_S hv.isPGroup (zpowers_le.mpr hv.mem_N)

theorem mem_U_cases {u : H} (hu : u ∈ h.U81 v) : u ∈ h.S ∨ ∃ s ∈ h.S, u = s * v := by
  have hu' : u ∈ ((h.U81 v : Subgroup H) : Set H) := hu
  rw [coe_mul_of_right_le_normalizer_left h.S (zpowers v) (zpowers_le.mpr hv.mem_N)] at hu'
  obtain ⟨s, hs, w, hw, hsw⟩ := hu'
  beta_reduce at hsw
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [← hsw, ← two_mul, zpow_mul, zpow_two]
    exact mul_mem hs (zpow_mem hv.sq_mem j)
  · right
    refine ⟨s * (v * v) ^ j, mul_mem hs (zpow_mem hv.sq_mem j), ?_⟩
    rw [← hsw, zpow_add, zpow_mul, zpow_two, zpow_one, mul_assoc]

theorem U_le_normalizer_F : h.U81 v ≤ normalizer (h.F32 : Set H) :=
  sup_le h.S_le_normalizer_F32 (zpowers_le.mpr (h.normalizer_S_le_normalizer_F32 hv.mem_N))

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB

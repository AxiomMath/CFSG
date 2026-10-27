module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Comm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_mem_inf_centralizer {V : Subgroup G} {s v : G} (hV : IsElemAbelian 2 V)
    (hs : s ∈ normalizer (V : Set G)) (hs2 : s * s = 1) (hv : v ∈ V) :
    ⁅v, s⁆ ∈ V ⊓ centralizer ({s} : Set G) := by
  have hss : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hcV : ⁅v, s⁆ ∈ V := by
    have h1 : s * v⁻¹ * s⁻¹ ∈ V := (mem_normalizer_iff.1 hs v⁻¹).1 (inv_mem hv)
    have : ⁅v, s⁆ = v * (s * v⁻¹ * s⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem hv h1
  refine Subgroup.mem_inf.2 ⟨hcV, mem_centralizer_singleton_iff.2 ?_⟩
  have hc2 : ⁅v, s⁆ * ⁅v, s⁆ = 1 := by rw [← sq]; exact hV.2 _ hcV
  have hci : ⁅v, s⁆⁻¹ = ⁅v, s⁆ := inv_eq_of_mul_eq_one_right hc2
  have e1 : s⁻¹ * s⁻¹ = 1 := by rw [hss, hs2]
  have h1 : s * ⁅v, s⁆ * s⁻¹ = ⁅v, s⁆⁻¹ := by
    rw [commutatorElement_def]
    calc s * (v * s * v⁻¹ * s⁻¹) * s⁻¹ = s * v * s * v⁻¹ * (s⁻¹ * s⁻¹) := by group
      _ = s * v * s * v⁻¹ := by rw [e1, mul_one]
      _ = s * v * s⁻¹ * v⁻¹ := by rw [hss]
      _ = (v * s * v⁻¹ * s⁻¹)⁻¹ := by group
  rw [hci] at h1
  calc ⁅v, s⁆ * s = (s * ⁅v, s⁆ * s⁻¹) * s := by rw [h1]
    _ = s * ⁅v, s⁆ := by group

theorem commutator_zpowers_eq [Finite G] {V : Subgroup G} {s : G} (hV : IsElemAbelian 2 V)
    (hs : s ∈ normalizer (V : Set G)) (hs2 : s * s = 1)
    (hcard : Nat.card V = Nat.card ↥(V ⊓ centralizer ({s} : Set G)) *
      Nat.card ↥(V ⊓ centralizer ({s} : Set G))) :
    ⁅V, zpowers s⁆ = V ⊓ centralizer ({s} : Set G) := by
  refine le_antisymm (Subgroup.commutator_le.2 fun v hv g hg => ?_) fun w hw => ?_
  · obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have : s ^ n = 1 := by
        rw [hk, ← two_mul, zpow_mul]
        have : s ^ (2 : ℤ) = 1 := by rw [zpow_two, hs2]
        rw [this, one_zpow]
      rw [this, commutatorElement_one_right]
      exact one_mem _
    · have : s ^ n = s := by
        have h2 : s ^ (2 : ℤ) = 1 := by rw [zpow_two, hs2]
        rw [hk, zpow_add, zpow_one, zpow_mul, h2, one_zpow, one_mul]
      rw [this]
      exact commutatorElement_mem_inf_centralizer hV hs hs2 hv
  · obtain ⟨hwV, hws⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨u, huV, hu⟩ := exists_comm_eq_of_card hV hs hs2 hcard hwV
      (mem_centralizer_singleton_iff.1 hws).symm
    rw [hu, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator huV (mem_zpowers s)

theorem relIndex_commutator_eq [Finite G] {V Z : Subgroup G} {s : G} (hV : IsElemAbelian 2 V)
    (hs : s ∈ normalizer (V : Set G)) (hs2 : s * s = 1) (hV10 : Nat.card V = 2 ^ 10)
    (hC : Nat.card ↥(V ⊓ centralizer ({s} : Set G)) = 2 ^ 5) (hZ4 : Nat.card Z = 4)
    (hZC : Z ≤ V ⊓ centralizer ({s} : Set G)) : Z.relIndex (⁅V, zpowers s⁆ ⊔ Z) = 8 := by
  have hcard : Nat.card V = Nat.card ↥(V ⊓ centralizer ({s} : Set G)) *
      Nat.card ↥(V ⊓ centralizer ({s} : Set G)) := by rw [hV10, hC]; norm_num
  rw [commutator_zpowers_eq hV hs hs2 hcard, sup_eq_left.2 hZC]
  have h := Subgroup.relIndex_mul_card Z (V ⊓ centralizer ({s} : Set G))
  rw [inf_eq_left.2 hZC, hZ4, hC] at h
  omega

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6

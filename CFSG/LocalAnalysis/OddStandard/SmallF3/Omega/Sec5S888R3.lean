module

public import Mathlib.GroupTheory.Index

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

theorem exists_mul_of_relIndex_dvd [Finite G] {Y D E : Subgroup G} (hEY : E ≤ Y)
    (hD : ∀ y ∈ Y, ∀ d ∈ D, y * d * y⁻¹ ∈ D) (hdvd : D.relIndex Y ∣ 8)
    (hE : 8 ≤ D.relIndex E) : ∀ y ∈ Y, ∃ e ∈ E, y * e⁻¹ ∈ D := by
  haveI hDnorm : (D.subgroupOf Y).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hD (g : G) g.2 (n : G) hn⟩
  have hsup : (D.subgroupOf Y).relIndex ((D.subgroupOf Y) ⊔ (E.subgroupOf Y))
      = (D.subgroupOf Y).relIndex (E.subgroupOf Y) :=
    Subgroup.relIndex_sup_left (H := E.subgroupOf Y) (K := D.subgroupOf Y)
  have hrel : (D.subgroupOf Y).relIndex (E.subgroupOf Y) = D.relIndex E :=
    Subgroup.relIndex_subgroupOf (H := D) (K := E) (L := Y) hEY
  have h8 : 8 ≤ (D.subgroupOf Y).relIndex ((D.subgroupOf Y) ⊔ (E.subgroupOf Y)) := by
    rw [hsup, hrel]; exact hE
  have hdv1 : (D.subgroupOf Y).relIndex ((D.subgroupOf Y) ⊔ (E.subgroupOf Y))
      ∣ (D.subgroupOf Y).index :=
    Subgroup.relIndex_dvd_index_of_le (H := D.subgroupOf Y)
      (K := (D.subgroupOf Y) ⊔ (E.subgroupOf Y)) le_sup_left
  have hdv2 : (D.subgroupOf Y).index ∣ 8 := hdvd
  have hr : (D.subgroupOf Y).relIndex ((D.subgroupOf Y) ⊔ (E.subgroupOf Y)) = 8 := by
    apply le_antisymm
    · exact Nat.le_of_dvd (n := 8) (by decide) (dvd_trans hdv1 hdv2)
    · exact h8
  have hidx : (D.subgroupOf Y).index = 8 := by
    rw [hr] at hdv1
    exact (Nat.dvd_antisymm hdv1 hdv2).symm
  have htower : (D.subgroupOf Y).relIndex ((D.subgroupOf Y) ⊔ (E.subgroupOf Y))
      * ((D.subgroupOf Y) ⊔ (E.subgroupOf Y)).relIndex ⊤
      = (D.subgroupOf Y).relIndex ⊤ :=
    Subgroup.relIndex_mul_relIndex (H := D.subgroupOf Y)
      (K := (D.subgroupOf Y) ⊔ (E.subgroupOf Y)) (L := ⊤) le_sup_left le_top
  rw [hr, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, hidx] at htower
  have hidx1 : ((D.subgroupOf Y) ⊔ (E.subgroupOf Y)).index = 1 := by
    apply Nat.mul_left_cancel (show 0 < 8 by decide)
    simpa using htower
  have htop : (D.subgroupOf Y) ⊔ (E.subgroupOf Y) = ⊤ :=
    Subgroup.index_eq_one.mp hidx1
  intro y hy
  have hy' : (⟨y, hy⟩ : Y) ∈ (D.subgroupOf Y) ⊔ (E.subgroupOf Y) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_left] at hy'
  obtain ⟨d, hd, e, he, hde⟩ := hy'
  refine ⟨(e : G), ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf).mp he
  · have hval : (d : G) * (e : G) = y := by
      simpa using congrArg Subtype.val hde
    have hdD : (d : G) ∈ D := (Subgroup.mem_subgroupOf).mp hd
    rw [← hval, mul_assoc, mul_inv_cancel, mul_one]
    exact hdD

end CFSG.OddStandard.SmallF3.Omega

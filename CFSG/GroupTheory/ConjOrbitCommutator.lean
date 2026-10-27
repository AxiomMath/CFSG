module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_closure_le_of_forall_eq_conj {H L : Subgroup G} (hLH : L ≤ H)
    (hL : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) {v : G} (hv : v ∈ H) {β : Set G}
    (hβ : ∀ x ∈ β, ∃ l ∈ L, x = l * v * l⁻¹) :
    ⁅Subgroup.closure β, Subgroup.closure β⁆ ≤ L := by
  classical
  set L' : Subgroup H := L.subgroupOf H with hL'
  have hN : L'.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hL g g.2 x hx⟩
  set φ : H →* H ⧸ L' := QuotientGroup.mk' L' with hφ
  set v' : H := ⟨v, hv⟩ with hv'
  have hβH : β ⊆ H := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := hβ x hx
    exact H.mul_mem (H.mul_mem (hLH hl) hv) (H.inv_mem (hLH hl))
  have hclH : Subgroup.closure β ≤ H := (Subgroup.closure_le H).mpr hβH
  have himg : ∀ a (ha : a ∈ Subgroup.closure β),
      φ ⟨a, hclH ha⟩ ∈ Subgroup.zpowers (φ v') := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨l, hl, rfl⟩ := hβ x hx
        have hl' : (⟨l, hLH hl⟩ : H) ∈ L' := by
          rw [Subgroup.mem_subgroupOf]
          exact hl
        have h1 : φ ⟨l, hLH hl⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hl'
        have heq : (⟨l * v * l⁻¹, hclH (Subgroup.subset_closure hx)⟩ : H) =
            ⟨l, hLH hl⟩ * v' * (⟨l, hLH hl⟩ : H)⁻¹ := rfl
        rw [heq, map_mul, map_mul, map_inv, h1, one_mul, inv_one, mul_one]
        exact Subgroup.mem_zpowers _
    | one =>
        have heq : (⟨1, hclH (Subgroup.one_mem _)⟩ : H) = 1 := rfl
        rw [heq, map_one]
        exact Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
        have heq : (⟨a * b, hclH (Subgroup.mul_mem _ ha hb)⟩ : H) =
            ⟨a, hclH ha⟩ * ⟨b, hclH hb⟩ := rfl
        rw [heq, map_mul]
        exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
        have heq : (⟨a⁻¹, hclH (Subgroup.inv_mem _ ha)⟩ : H) = (⟨a, hclH ha⟩ : H)⁻¹ := rfl
        rw [heq, map_inv]
        exact Subgroup.inv_mem _ iha
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hcomm : Commute (φ ⟨a, hclH ha⟩) (φ ⟨b, hclH hb⟩) := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (himg a ha)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (himg b hb)
    rw [← hi, ← hj]
    exact Commute.zpow_zpow_self (φ v') i j
  have hker : (⁅(⟨a, hclH ha⟩ : H), ⟨b, hclH hb⟩⁆ : H) ∈ L' := by
    rw [← QuotientGroup.eq_one_iff]
    change φ ⁅(⟨a, hclH ha⟩ : H), ⟨b, hclH hb⟩⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  rw [Subgroup.mem_subgroupOf] at hker
  exact hker

theorem image_conj_eq_of_eq_conjOrbit {L : Subgroup G} {c : G} {γ : Set G}
    (hγ : γ = {x | ∃ l ∈ L, x = l * c * l⁻¹}) {l : G} (hl : l ∈ L) :
    (fun y => l * y * l⁻¹) '' γ = γ := by
  subst hγ
  ext x
  constructor
  · rintro ⟨y, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨l * m, L.mul_mem hl hm, ?_⟩
    show l * (m * c * m⁻¹) * l⁻¹ = l * m * c * (l * m)⁻¹
    group
  · rintro ⟨m, hm, rfl⟩
    refine ⟨l⁻¹ * m * c * (l⁻¹ * m)⁻¹, ⟨l⁻¹ * m, L.mul_mem (L.inv_mem hl) hm, rfl⟩, ?_⟩
    show l * (l⁻¹ * m * c * (l⁻¹ * m)⁻¹) * l⁻¹ = m * c * m⁻¹
    group

end CFSG.GroupTheory

end

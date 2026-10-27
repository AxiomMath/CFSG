module

public import CFSG.LargeExtraspecial.AS35ESixNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem BAt_eq_BSet (hS : S.SixFourConcl)
    (h69 : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g ⊆ S.BSet) {g : G}
    (hg : g * S.z * g⁻¹ ∈ S.BSet) : S.BAt g = S.BSet := by
  refine le_antisymm (h69 g hg) fun b hb => ?_
  have hz : (1 : G) * S.z * 1⁻¹ ∈ S.BAt g := S.mem_BAt_symm hS hg
  have h1 : g⁻¹ * S.z * g⁻¹⁻¹ ∈ S.BSet := by
    have := (S.mem_BAt_iff).mp hz
    rwa [show g⁻¹ * (1 * S.z * 1⁻¹) * g = g⁻¹ * S.z * g⁻¹⁻¹ by group] at this
  rw [S.mem_BAt_iff]
  apply h69 g⁻¹ h1
  have := S.conj_mem_BAt (c := g⁻¹) hb
  rwa [mul_one, inv_inv] at this

theorem orderOf_mul_mem_of_mem_BSet (hS : S.SixFourConcl)
    (h69 : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g ⊆ S.BSet)
    (h66 : ∀ s ∈ S.DSet, ∀ t ∈ S.DSet, orderOf (s * t) ∈ ({1, 2, 3} : Set ℕ)) {a b : G}
    (ha : a ∈ S.BSet) (hb : b ∈ S.BSet) : orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨g, rfl⟩ : ∃ g : G, g * S.z * g⁻¹ = a := by
    obtain ⟨k, -, hak⟩ := ha
    exact S.exists_conj_of_mem_DAt hak
  rw [← S.BAt_eq_BSet hS h69 ha] at hb
  obtain ⟨j, hj, hbj⟩ := hb
  have haj := S.mem_DAt_symm hS hj
  rw [mem_DAt] at haj hbj
  have h := h66 _ haj _ hbj
  rwa [show j⁻¹ * (g * S.z * g⁻¹) * j * (j⁻¹ * b * j) =
      j⁻¹ * (g * S.z * g⁻¹ * b) * j⁻¹⁻¹ by group, orderOf_conj_eq] at h

end Setting

end CFSG.LargeExtraspecial

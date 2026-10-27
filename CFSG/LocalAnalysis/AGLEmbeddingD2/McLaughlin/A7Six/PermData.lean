module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open Equiv Equiv.Perm

structure PermData where
  D : Subgroup (Perm (Fin 7))
  E : Subgroup (Perm (Fin 7))
  P : Fin 3 → Subgroup (Perm (Fin 7))
  PN : Subgroup (Perm (Fin 7))
  card_D : Nat.card D = 16
  card_E : Nat.card E = 8
  card_P : ∀ i, Nat.card (P i) = 24
  card_PN : Nat.card PN = 48
  E_le_D : E ≤ D
  E_le_P : ∀ i, E ≤ P i
  D_le_PN : D ≤ PN
  swap_mem_E : swap 0 2 ∈ E
  D_fix : ∀ σ ∈ D, σ 6 = 6
  P_notNormal : ∀ i, ∃ g ∈ P i ⊓ alternatingGroup (Fin 7), ∃ e ∈ E, g * e * g⁻¹ ∉ E
  PN_notNormal : ∃ g ∈ PN ⊓ alternatingGroup (Fin 7), ∃ d ∈ D, g * d * g⁻¹ ∉ D
  D_trans : ∀ σ ∈ D, σ * σ = 1 → (∀ i, σ i ≠ i → swap i (σ i) ∈ D) → σ ∈ E
  D_stab : ∀ σ ∈ D, σ 0 ∈ ({0, 2} : Finset (Fin 7)) → σ 2 ∈ ({0, 2} : Finset (Fin 7)) →
    σ 1 ∈ ({1, 3} : Finset (Fin 7)) → σ 3 ∈ ({1, 3} : Finset (Fin 7)) →
    σ 4 ∈ ({4, 5} : Finset (Fin 7)) → σ 5 ∈ ({4, 5} : Finset (Fin 7)) → σ ∈ E
  E_pairs : ∀ σ ∈ E, σ 0 ∈ ({0, 2} : Finset (Fin 7)) ∧ σ 2 ∈ ({0, 2} : Finset (Fin 7)) ∧
    σ 1 ∈ ({1, 3} : Finset (Fin 7)) ∧ σ 3 ∈ ({1, 3} : Finset (Fin 7)) ∧
    σ 4 ∈ ({4, 5} : Finset (Fin 7)) ∧ σ 5 ∈ ({4, 5} : Finset (Fin 7))
  gen_P : alternatingGroup (Fin 7) ≤
    Subgroup.closure (⋃ i, ((P i ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) :
      Set (Perm (Fin 7))))
  gen_PN : ∀ i, alternatingGroup (Fin 7) ≤
    Subgroup.closure (((PN ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) :
      Set (Perm (Fin 7))) ∪ (P i ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))))

theorem isSolvable_of_index_le_four {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hH : Group.IsSolvable ↥H) (hidx : H.index ≤ 4) : Group.IsSolvable G := by
  let f := MulAction.toPermHom G (G ⧸ H)
  have hperm : Group.IsSolvable (Perm (G ⧸ H)) := Equiv.Perm.isSolvable (by exact hidx)
  have hker : f.ker ≤ H := by
    rw [← Subgroup.normalCore_eq_ker]
    exact Subgroup.normalCore_le H
  have : Group.IsSolvable ↥f.ker :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hker)
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)

theorem isSolvable_of_three_mul {Q P : Subgroup (Perm (Fin 7))} (hQP : Q ≤ P)
    (hQ : IsPGroup 2 ↥Q) (hcard : Nat.card P = 3 * Nat.card Q) : Group.IsSolvable ↥P := by
  have h2 : IsPGroup 2 ↥(Q.subgroupOf P) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have := h2.isNilpotent
  refine isSolvable_of_index_le_four (Q.subgroupOf P) inferInstance ?_
  have h1 := Subgroup.relIndex_mul_card Q P
  rw [inf_eq_left.mpr hQP, hcard] at h1
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have h3 : Q.relIndex P = 3 := Nat.eq_of_mul_eq_mul_right hpos h1
  show Q.relIndex P ≤ 4
  omega

namespace PermData

variable (pd : PermData)

theorem isPGroup_E : IsPGroup 2 ↥pd.E := IsPGroup.of_card (n := 3) (by rw [pd.card_E]; rfl)

theorem isPGroup_D : IsPGroup 2 ↥pd.D := IsPGroup.of_card (n := 4) (by rw [pd.card_D]; rfl)

theorem solv_P (i : Fin 3) : Group.IsSolvable ↥(pd.P i) :=
  isSolvable_of_three_mul (pd.E_le_P i) pd.isPGroup_E (by rw [pd.card_P i, pd.card_E])

theorem solv_PN : Group.IsSolvable ↥pd.PN :=
  isSolvable_of_three_mul pd.D_le_PN pd.isPGroup_D (by rw [pd.card_PN, pd.card_D])

end PermData

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six

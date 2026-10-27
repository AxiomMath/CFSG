module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.QuasisimpleTwoNonab
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open Equiv Equiv.Perm

def a6r : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5
def a6s : Perm (Fin 6) := swap 0 2 * swap 4 5

def a6D8 : Finset (Perm (Fin 6)) :=
  {1, a6r, a6r * a6r, a6r * a6r * a6r, a6s, a6s * a6r, a6s * a6r * a6r, a6s * a6r * a6r * a6r}

theorem a6D8_mul : ∀ a ∈ a6D8, ∀ b ∈ a6D8, a * b ∈ a6D8 := by
  unfold a6D8 a6r a6s
  decide +kernel

theorem a6D8_card : a6D8.card = 8 := by
  unfold a6D8 a6r a6s
  decide +kernel


theorem a6D8_inv : ∀ a ∈ a6D8, a⁻¹ ∈ a6D8 := by
  unfold a6D8 a6r a6s
  decide +kernel

theorem a6D8_even : ∀ a ∈ a6D8, a ∈ alternatingGroup (Fin 6) := by
  intro a ha
  rw [mem_alternatingGroup]
  revert a ha
  unfold a6D8 a6r a6s
  decide +kernel

def a6Q : Subgroup (Perm (Fin 6)) where
  carrier := ↑a6D8
  mul_mem' := fun {a b} ha hb => a6D8_mul a ha b hb
  one_mem' := by simp [a6D8]
  inv_mem' := fun {a} ha => a6D8_inv a ha

theorem a6Q_le : a6Q ≤ alternatingGroup (Fin 6) := fun a ha => a6D8_even a ha

theorem a6Q_card : Nat.card a6Q = 8 := by
  have : Nat.card a6Q = a6D8.card := Nat.card_eq_finsetCard a6D8
  rw [this, a6D8_card]

theorem a6Q_isPGroup : IsPGroup 2 a6Q := IsPGroup.of_card (n := 3) (by rw [a6Q_card]; norm_num)

theorem a6r_mem : a6r ∈ a6Q := by
  show a6r ∈ (↑a6D8 : Set (Perm (Fin 6)))
  simp [a6D8]

theorem a6s_mem : a6s ∈ a6Q := by
  show a6s ∈ (↑a6D8 : Set (Perm (Fin 6)))
  simp [a6D8]

theorem a6r_s_noncomm : a6r * a6s ≠ a6s * a6r := by
  unfold a6r a6s
  decide +kernel

theorem isQuasisimpleTwoNonab_alternatingGroup_six :
    IsQuasisimpleTwoNonab (alternatingGroup (Fin 6)) := by
  refine isQuasisimpleTwoNonab_of_simple (alternatingGroup.isSimpleGroup (by simp)) ?_ ?_
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  · refine ⟨a6Q.subgroupOf (alternatingGroup (Fin 6)), a6Q_isPGroup.comap_subtype,
      ⟨a6r, a6Q_le a6r_mem⟩, a6r_mem, ⟨a6s, a6Q_le a6s_mem⟩, a6s_mem, fun h => a6r_s_noncomm ?_⟩
    exact congrArg Subtype.val h

end CFSG.AGLEmbeddingD2.Tits.GN516

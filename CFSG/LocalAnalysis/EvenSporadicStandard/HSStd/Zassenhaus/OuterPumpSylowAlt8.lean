module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Equiv Equiv.Perm Subgroup

namespace Alt8Sixteen

@[expose] def gen (i : Fin 4) : Perm (Fin 8) :=
  match i with
  | 0 => swap 0 1 * swap 2 3
  | 1 => swap 0 2 * swap 1 3
  | 2 => swap 4 5 * swap 6 7
  | 3 => swap 4 6 * swap 5 7

theorem gen_mem (i : Fin 4) : gen i ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup]
  fin_cases i <;>
    simp only [gen, sign_mul, sign_swap (by decide : (0 : Fin 8) ≠ 1),
      sign_swap (by decide : (2 : Fin 8) ≠ 3), sign_swap (by decide : (0 : Fin 8) ≠ 2),
      sign_swap (by decide : (1 : Fin 8) ≠ 3), sign_swap (by decide : (4 : Fin 8) ≠ 5),
      sign_swap (by decide : (6 : Fin 8) ≠ 7), sign_swap (by decide : (4 : Fin 8) ≠ 6),
      sign_swap (by decide : (5 : Fin 8) ≠ 7)] <;> decide

@[expose] def vec (v : Fin 2 × Fin 2 × Fin 2 × Fin 2) : alternatingGroup (Fin 8) :=
  (⟨gen 0, gen_mem 0⟩ : alternatingGroup (Fin 8)) ^ (v.1 : ℕ) *
    (⟨gen 1, gen_mem 1⟩ : alternatingGroup (Fin 8)) ^ (v.2.1 : ℕ) *
    (⟨gen 2, gen_mem 2⟩ : alternatingGroup (Fin 8)) ^ (v.2.2.1 : ℕ) *
    (⟨gen 3, gen_mem 3⟩ : alternatingGroup (Fin 8)) ^ (v.2.2.2 : ℕ)

theorem vec_injective : Function.Injective vec := by
  decide +kernel

theorem vec_sq : ∀ v, vec v * vec v = 1 := by
  decide +kernel

theorem vec_mul : ∀ v w, ∃ u, vec v * vec w = vec u := by
  decide +kernel

theorem vec_one : ∃ u, vec u = 1 := ⟨(0, 0, 0, 0), by decide +kernel⟩

@[expose] def E16 : Subgroup (alternatingGroup (Fin 8)) where
  carrier := Set.range vec
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact (vec_mul v w).imp fun u h => h.symm
  one_mem' := vec_one
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨v, by rw [inv_eq_of_mul_eq_one_right (vec_sq v)]⟩

theorem card_E16 : Nat.card E16 = 16 := by
  have : Nat.card E16 = Nat.card (Fin 2 × Fin 2 × Fin 2 × Fin 2) :=
    (Nat.card_congr (Equiv.ofInjective vec vec_injective)).symm
  rw [this]
  simp

theorem sq_of_mem_E16 {x : alternatingGroup (Fin 8)} (hx : x ∈ E16) : x * x = 1 := by
  obtain ⟨v, rfl⟩ := hx
  exact vec_sq v

end Alt8Sixteen

theorem exists_elemAbelian_sixteen_of_equiv_alt8 {G : Type*} [Group G] {J : Subgroup G}
    (e : ↥J ≃* alternatingGroup (Fin 8)) :
    ∃ E : Subgroup G, E ≤ J ∧ Nat.card E = 16 ∧ ∀ x ∈ E, x * x = 1 := by
  refine ⟨(Alt8Sixteen.E16.map e.symm.toMonoidHom).map J.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨_, _, rfl⟩
    exact Subtype.mem _
  · rw [Subgroup.card_map_of_injective J.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, Alt8Sixteen.card_E16]
  · rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have := Alt8Sixteen.sq_of_mem_E16 hz
    have h2 : e.symm z * e.symm z = 1 := by rw [← map_mul, this, map_one]
    simpa using congrArg Subtype.val h2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

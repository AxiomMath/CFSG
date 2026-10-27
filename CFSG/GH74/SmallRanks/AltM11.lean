module

public import CFSG.GH74.SmallRanks.Basic
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order

public section

namespace CFSG.GH74.SmallRanks

open CFSG.Open

@[expose] def alt7Elt : alternatingGroup (Fin 7) :=
  ⟨List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5], by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

theorem orderOf_alt7Elt : orderOf alt7Elt = 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (n := 1)
  · decide
  · decide

theorem factorization_two_card_alt7 :
    (Nat.card (alternatingGroup (Fin 7))).factorization 2 = 3 := by
  have h : Nat.card (alternatingGroup (Fin 7)) = 2 ^ 3 * 315 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h]
  exact factorization_two_pow_mul_odd (by decide)

theorem twoRank_alternatingGroup_seven_le_two : twoRank (alternatingGroup (Fin 7)) ≤ 2 :=
  twoRank_le_two_of_orderOf alt7Elt 2 orderOf_alt7Elt factorization_two_card_alt7

@[expose] def m11Elt : Equiv.Perm (Fin 11) :=
  (List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]) *
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]) *
    (List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]) *
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]) *
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]) *
    (List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]) *
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]) *
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8])

theorem m11Elt_mem : m11Elt ∈ CFSG.Blueprint.NativeSporadic.M11 := by
  unfold CFSG.Blueprint.NativeSporadic.M11
  have ha : (List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] *
      List.formPerm [7, 8] : Equiv.Perm (Fin 11)) ∈ Subgroup.closure
      {(List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] *
        List.formPerm [7, 8] : Equiv.Perm (Fin 11)),
      (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8] : Equiv.Perm (Fin 11))} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8] :
      Equiv.Perm (Fin 11)) ∈ Subgroup.closure
      {(List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] *
        List.formPerm [7, 8] : Equiv.Perm (Fin 11)),
      (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8] : Equiv.Perm (Fin 11))} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  unfold m11Elt
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ha hb) ha) hb) hb) ha) hb) hb

theorem orderOf_m11Elt : orderOf m11Elt = 2 ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (n := 2)
  · decide +kernel
  · decide +kernel

theorem factorization_two_card_M11 :
    (Nat.card CFSG.Blueprint.NativeSporadic.M11).factorization 2 = 4 := by
  rw [CFSG.Semidihedral.GL2Recognition.card_nativeM11, show (7920 : ℕ) = 2 ^ 4 * 495 by norm_num]
  exact factorization_two_pow_mul_odd (by decide)

theorem twoRank_M11_le_two :
    twoRank CFSG.Blueprint.NativeSporadic.M11 ≤ 2 := by
  have : Finite CFSG.Blueprint.NativeSporadic.M11 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Semidihedral.GL2Recognition.card_nativeM11]; norm_num)
  refine twoRank_le_two_of_orderOf (⟨m11Elt, m11Elt_mem⟩ : CFSG.Blueprint.NativeSporadic.M11) 3 ?_
    factorization_two_card_M11
  rw [← Subgroup.orderOf_coe]
  exact orderOf_m11Elt

end CFSG.GH74.SmallRanks

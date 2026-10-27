module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveTransfer
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG.Blueprint CFSG.Sporadic.Bridge

@[expose] def m12GenA : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

@[expose] def m12GenB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

@[expose] def m12Gen (i : ℕ) : Equiv.Perm (Fin 12) := if i = 0 then m12GenA else m12GenB

@[expose] def m12Tau : List (ℕ × Bool) :=
  [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
   (1, false), (0, true), (1, false)]

set_option maxRecDepth 100000 in
theorem m12_pow_eleven : (m12GenA * m12GenB) ^ 11 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12_ne_one : m12GenA * m12GenB ≠ 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12Tau_pow_five : wordProd m12Gen m12Tau ^ 5 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12Tau_conj :
    wordProd m12Gen m12Tau * (m12GenA * m12GenB) =
      (m12GenA * m12GenB) ^ 3 * wordProd m12Gen m12Tau := by
  decide +kernel

theorem m12Gen_mem (i : ℕ) : m12Gen i ∈ NativeSporadic.M12 := by
  unfold m12Gen
  split
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def m12Y : NativeSporadic.M12 :=
  ⟨m12GenA * m12GenB, Subgroup.mul_mem _ (m12Gen_mem 0) (m12Gen_mem 1)⟩

@[expose] def m12T : NativeSporadic.M12 := ⟨wordProd m12Gen m12Tau, wordProd_mem m12Gen_mem _⟩

theorem coe_m12Y : ((m12Y : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = m12GenA * m12GenB := rfl

theorem coe_m12T : ((m12T : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = wordProd m12Gen m12Tau :=
  rfl

theorem m12Y_pow : m12Y ^ 11 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_m12Y, Subgroup.coe_one]
  exact m12_pow_eleven

theorem m12Y_ne : m12Y ≠ 1 := by
  intro h
  apply m12_ne_one
  have := congrArg Subtype.val h
  rwa [coe_m12Y, Subgroup.coe_one] at this

theorem m12T_pow : m12T ^ 5 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_m12T, Subgroup.coe_one]
  exact m12Tau_pow_five

theorem m12T_conj : m12T * m12Y * m12T⁻¹ = m12Y ^ 3 := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, coe_m12Y, coe_m12T]
  exact m12Tau_conj

theorem frobData_M12 {Q : Type} [Group Q]
    (hQ : NativeSporadic.IsSporadic Q .M12) : FrobData Q := by
  obtain ⟨e0⟩ := hQ
  let e : Q ≃* ↥NativeSporadic.M12 := e0
  refine ⟨e.symm m12Y, e.symm m12T, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, m12Y_pow, map_one]
  · exact fun h => m12Y_ne (e.symm.injective (by rw [h, map_one]))
  · rw [← map_pow, m12T_pow, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, m12T_conj, map_pow]
  · have hcard : Nat.card Q = 95040 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Schreier.m12_card
    rw [hcard]
    norm_num

end CFSG.CGT.PushingUpLit.CGT6M

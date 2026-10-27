module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GF2Type.Smith1979.TriPlus

theorem perm3_exists_fixed {x : Equiv.Perm (Fin 3)} (hx : x * x = 1) : ∃ j, x j = j := by
  revert x
  decide +kernel

private theorem perm3_cube_eq_one_of_sq_ne_one (x : Equiv.Perm (Fin 3))
    (hx : x * x ≠ 1) : x ^ 3 = 1 := by
  revert x
  decide +kernel

private theorem perm3_exists_three_cycle {x y : Equiv.Perm (Fin 3)} {i k : Fin 3}
    (hxi : x i ≠ i) (hxk : x k = k) (hyk : y k ≠ k) :
    ∃ z : Equiv.Perm (Fin 3), (z = x ∨ z = y ∨ z = x * y) ∧ z ^ 3 = 1 ∧ z ≠ 1 := by
  revert x y i k
  decide +kernel

private theorem perm3_exists_cube_eq_one_ne_one {H : Subgroup (Equiv.Perm (Fin 3))}
    (h : ∀ k : Fin 3, ∃ x ∈ H, x k ≠ k) :
    ∃ z ∈ H, z ^ 3 = 1 ∧ z ≠ 1 := by
  obtain ⟨x, hxH, hx0⟩ := h 0
  by_cases hx2 : x * x = 1
  · obtain ⟨k, hk⟩ := perm3_exists_fixed hx2
    obtain ⟨y, hyH, hyk⟩ := h k
    obtain ⟨z, hz, hz3, hz1⟩ :=
      perm3_exists_three_cycle (x := x) (y := y) (i := 0) (k := k) hx0 hk hyk
    refine ⟨z, ?_, hz3, hz1⟩
    rcases hz with rfl | rfl | rfl
    · exact hxH
    · exact hyH
    · exact H.mul_mem hxH hyH
  · exact ⟨x, hxH, perm3_cube_eq_one_of_sq_ne_one x hx2,
      fun h1 => hx0 (by simp [h1])⟩

theorem perm3_card_of_forall_moved {H : Subgroup (Equiv.Perm (Fin 3))}
    (h : ∀ k : Fin 3, ∃ x ∈ H, x k ≠ k) : Nat.card H = 3 ∨ Nat.card H = 6 := by
  obtain ⟨z, hzH, hz3, hz1⟩ := perm3_exists_cube_eq_one_ne_one h
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have h3dvd : 3 ∣ Nat.card H := by
    simpa [hzord] using Subgroup.orderOf_dvd_natCard H hzH
  have hcard6 : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by decide +kernel
  have hdvd6 : Nat.card H ∣ 6 := by
    simpa [hcard6] using Subgroup.card_subgroup_dvd_card H
  have hle : Nat.card H ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
  have hge : 3 ≤ Nat.card H := Nat.le_of_dvd (by norm_num) h3dvd
  set n := Nat.card H
  have hle' : n ≤ 6 := hle
  have hge' : 3 ≤ n := hge
  interval_cases n <;> simp_all

private theorem perm3_exists_pow_apply_eq {z : Equiv.Perm (Fin 3)} {i j : Fin 3}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : ∃ k : Fin 3, (z ^ (k : ℕ)) i = j := by
  revert z i j
  decide +kernel

theorem perm3_exists_apply_eq {H : Subgroup (Equiv.Perm (Fin 3))}
    (h : ∀ k : Fin 3, ∃ x ∈ H, x k ≠ k) (i j : Fin 3) : ∃ x ∈ H, x i = j := by
  obtain ⟨z, hzH, hz3, hz1⟩ := perm3_exists_cube_eq_one_ne_one h
  obtain ⟨k, hk⟩ := perm3_exists_pow_apply_eq (z := z) (i := i) (j := j) hz3 hz1
  exact ⟨z ^ (k : ℕ), H.pow_mem hzH (k : ℕ), hk⟩

end CFSG.GF2Type.Smith1979.TriPlus

end

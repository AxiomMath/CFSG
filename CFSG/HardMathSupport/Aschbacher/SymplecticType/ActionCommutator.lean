module


public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.HardMathSupport.Aschbacher.SymplecticType

open Subgroup

@[expose] def actionCommutator (V : Type*) [Group V] (X : Set (MulAut V)) : Subgroup V :=
  closure {u | ∃ g ∈ X, ∃ v : V, u = v⁻¹ * g v}

theorem actionCommutator_eq_bot_of_fixed_points_eq (V : Type*) [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1)
    (x : MulAut V) (hx : ∃ k : ℕ, orderOf x = 2 ^ k)
    (hC : {v : V | x v = v} = {v : V | (x ^ 2) v = v}) :
    actionCommutator V {x} = ⊥ := by
  obtain ⟨k, hk⟩ := hx
  have hinv : ∀ w : V, w⁻¹ = w := fun w => by
    rw [inv_eq_iff_mul_eq_one, ← sq]; exact hV w
  have hsq : ∀ w : V, w * w = 1 := fun w => by rw [← sq]; exact hV w
  obtain ⟨T, hT⟩ : ∃ T : V → V, ∀ v, T v = v⁻¹ * x v := ⟨_, fun v => rfl⟩

  have hTT : ∀ v, T (T v) = v⁻¹ * x (x v) := by
    intro v
    rw [hT (T v), hT v]
    simp only [map_mul, map_inv, hinv, mul_inv, inv_inv]
    rw [show v * x v * (x v * x (x v)) = v * x (x v) * (x v * x v) by ac_rfl, hsq, mul_one]

  have hfix : ∀ w, T w = 1 ↔ T (T w) = 1 := by
    intro w
    have h := Set.ext_iff.1 hC w
    simp only [Set.mem_setOf_eq] at h
    have h2 : (x ^ 2) w = x (x w) := by rw [sq, MulAut.mul_apply]
    rw [h2] at h
    rw [hTT w, hT w, inv_mul_eq_one, inv_mul_eq_one]
    constructor
    · intro e
      exact (h.1 e.symm).symm
    · intro e
      exact (h.2 e.symm).symm
  have hpow : ∀ j v, T^[2 ^ j] v = (x ^ (2 ^ j)) v * v⁻¹ := by
    intro j
    induction j with
    | zero => intro v; simp [hT, mul_comm]
    | succ j ih =>
      intro v
      have e : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; omega
      rw [e, Function.iterate_add_apply, pow_add, MulAut.mul_apply]
      simp only [ih]
      generalize x ^ 2 ^ j = y
      simp only [map_mul, map_inv, hinv]
      rw [show y (y v) * y v * (y v * v) = y (y v) * v * (y v * y v) by ac_rfl, hsq, mul_one]

  have hall : ∀ n v, T^[1 + n] v = 1 → T v = 1 := by
    intro n
    induction n with
    | zero => intro v h; simpa using h
    | succ n ih =>
      intro v h
      rw [show 1 + (n + 1) = n + 1 + 1 by omega, Function.iterate_succ_apply',
        Function.iterate_succ_apply'] at h
      have h2 : T (T^[n] v) = 1 := (hfix _).2 h
      apply ih
      rw [show 1 + n = n + 1 by omega, Function.iterate_succ_apply']
      exact h2
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hone : ∀ v, T^[2 ^ k] v = 1 := fun v => by
    rw [hpow, ← hk, pow_orderOf_eq_one]
    simp
  have hTv : ∀ v, v⁻¹ * x v = 1 := fun v => by
    rw [← hT]; exact hall (2 ^ k - 1) v (by rw [show 1 + (2 ^ k - 1) = 2 ^ k by omega]; exact hone v)
  unfold actionCommutator
  refine eq_bot_iff.2 ((Subgroup.closure_le _).2 ?_)
  rintro u ⟨g, hg, v, rfl⟩
  rw [Set.mem_singleton_iff] at hg
  subst hg
  simp [hTv]

end CFSG.HardMathSupport.Aschbacher.SymplecticType

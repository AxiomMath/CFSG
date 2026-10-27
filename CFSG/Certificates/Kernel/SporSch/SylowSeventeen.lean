module

public import CFSG.Certificates.Kernel.SporSch.SylowCount
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.SylowCount

open Finset

variable {G : Type*} [Group G]

theorem conj_pow_seventeen {z g : G} (hz : orderOf z = 17) (hg : g * z * g⁻¹ = z ^ 2) {k : ℕ}
    (hk0 : 0 < k) (hk : k < 17) : IsConj z (z ^ k) ∨ IsConj (z ^ 3) (z ^ k) := by
  have st : ∀ k, IsConj (z ^ k) (z ^ (2 * k % 17)) := fun k => by
    refine isConj_iff.2 ⟨g, ?_⟩
    rw [← conj_pow, hg, ← pow_mul, ← hz, pow_mod_orderOf]
  have c1 := st 1
  have c2 := st 2
  have c4 := st 4
  have c8 := st 8
  have c16 := st 16
  have c15 := st 15
  have c13 := st 13
  have c3 := st 3
  have c6 := st 6
  have c12 := st 12
  have c7 := st 7
  have c14 := st 14
  have c11 := st 11
  have c5 := st 5
  simp only [Nat.reduceMul, Nat.reduceMod, pow_one] at c1 c2 c4 c8 c16 c15 c13
  simp only [Nat.reduceMul, Nat.reduceMod] at c3 c6 c12 c7 c14 c11 c5
  have a4 := c1.trans c2
  have a8 := a4.trans c4
  have a16 := a8.trans c8
  have a15 := a16.trans c16
  have a13 := a15.trans c15
  have a9 := a13.trans c13
  have b12 := c3.trans c6
  have b7 := b12.trans c12
  have b14 := b7.trans c7
  have b11 := b14.trans c14
  have b5 := b11.trans c11
  have b10 := b5.trans c5
  interval_cases k
  · exact Or.inl (isConj_iff.2 ⟨1, by simp⟩)
  · exact Or.inl c1
  · exact Or.inr (IsConj.refl _)
  · exact Or.inl a4
  · exact Or.inr b5
  · exact Or.inr c3
  · exact Or.inr b7
  · exact Or.inl a8
  · exact Or.inl a9
  · exact Or.inr b10
  · exact Or.inr b11
  · exact Or.inr b12
  · exact Or.inl a13
  · exact Or.inr b14
  · exact Or.inl a15
  · exact Or.inl a16

theorem cover_seventeen {z g x : G} (hz : orderOf z = 17) (hg : g * z * g⁻¹ = z ^ 2)
    (hx : ∃ i < 17, IsConj (z ^ i) x) (hx1 : orderOf x = 17) :
    IsConj z x ∨ IsConj (z ^ 3) x := by
  obtain ⟨i, hi, hc⟩ := hx
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [pow_zero, isConj_one_right] at hc
    rw [hc, orderOf_one] at hx1
    omega
  · rcases conj_pow_seventeen hz hg hi0 hi with h | h
    · exact Or.inl (h.trans hc)
    · exact Or.inr (h.trans hc)

variable [Fintype G]

open scoped Classical

theorem card_class_mul_le (j : G) :
    #(univ.filter (IsConj j)) * orderOf j ≤ Fintype.card G := by
  rw [← card_conj_mul_card_comm j]
  refine Nat.mul_le_mul_left _ ?_
  have hinj : Set.InjOn (fun i : ℕ => j ^ i) (range (orderOf j)) := fun a ha b hb h =>
    pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) h
  rw [← card_range (orderOf j), ← card_image_of_injOn hinj]
  refine card_le_card fun c hc => ?_
  obtain ⟨i, -, rfl⟩ := mem_image.1 hc
  rw [mem_filter]
  exact ⟨mem_univ _, (Commute.self_pow j i).symm.eq⟩

variable (a : G) (Q : G → G → Prop)
  (hQ : ∀ g x y, Q (g * x * g⁻¹) (g * y * g⁻¹) ↔ Q x y)
  (Zr : G → Prop) (hZr : ∀ g z, Zr (g * z * g⁻¹) ↔ Zr z)

include hQ hZr in
theorem pair_count_le (Z : List G) (hZ : ∀ z, Zr z → ∃ j ∈ Z, IsConj j z) :
    #(univ.filter (IsConj a)) * #(univ.filter fun y => Zr (a * y) ∧ Q a y) ≤
      (Z.map fun j => #(univ.filter fun z => IsConj j z) *
        #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * j))).sum := by
  have hS : #(univ.filter (IsConj a)) * #(univ.filter fun y => Zr (a * y) ∧ Q a y) =
      ∑ x, ∑ y, if IsConj a x ∧ Zr (x * y) ∧ Q x y then 1 else 0 := by
    rw [← smul_eq_mul, ← sum_const, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [← card_partners_conj a Q hQ Zr hZr hx, card_filter]
      refine sum_congr rfl fun y _ => ?_
      simp only [hx, true_and]
    · exact (sum_eq_zero fun y _ => ite_eq_right fun h => hx h.1).symm
  have hT : (∑ x, ∑ y, if IsConj a x ∧ Zr (x * y) ∧ Q x y then 1 else 0) =
      ∑ z, if Zr z then #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z)) else 0 := by
    have : ∀ x : G, (∑ y, if IsConj a x ∧ Zr (x * y) ∧ Q x y then 1 else 0) =
        ∑ z, if IsConj a x ∧ Zr z ∧ Q x (x⁻¹ * z) then 1 else 0 := fun x => by
      refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun y => ?_
      simp [Equiv.coe_mulLeft]
    rw [Fintype.sum_congr _ _ this, sum_comm]
    refine sum_congr rfl fun z _ => ?_
    split_ifs with hz
    · rw [card_filter]
      refine sum_congr rfl fun x _ => ?_
      simp [hz]
    · exact sum_eq_zero fun x _ => by simp [hz]
  have hU : ∀ L : List G,
      (∑ z, if ∃ j ∈ L, IsConj j z then #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z))
        else 0) ≤
      (L.map fun j => #(univ.filter fun z => IsConj j z) *
        #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * j))).sum := by
    intro L
    induction L with
    | nil => simp
    | cons j L ih =>
      rw [List.map_cons, List.sum_cons]
      have hj : (∑ z, if IsConj j z then #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * j))
          else 0) = #(univ.filter fun z => IsConj j z) *
            #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * j)) := by
        rw [← smul_eq_mul, ← sum_const, sum_filter]
      have hsplit : ∀ z : G, (if ∃ i ∈ j :: L, IsConj i z then
          #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z)) else 0) ≤
          (if IsConj j z then #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * j)) else 0) +
          (if ∃ i ∈ L, IsConj i z then
            #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z)) else 0) := fun z => by
        by_cases hjz : IsConj j z
        · rw [ite_eq_left ⟨j, List.mem_cons_self, hjz⟩, ite_eq_left hjz,
            card_conjugates_conj a Q hQ hjz]
          exact Nat.le_add_right _ _
        · rw [ite_eq_right hjz, zero_add]
          simp only [List.mem_cons, exists_eq_or_imp, hjz, false_or, le_refl]
      refine (sum_le_sum fun z _ => hsplit z).trans ?_
      rw [sum_add_distrib, hj]
      exact Nat.add_le_add_left ih _
  rw [hS, hT]
  refine (sum_le_sum fun z _ => ?_).trans (hU Z)
  by_cases hz : Zr z
  · rw [ite_eq_left hz, ite_eq_left (hZ z hz)]
  · rw [ite_eq_right hz]
    exact Nat.zero_le _

end CFSG.KS.SylowCount

end

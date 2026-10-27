module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.ComponentClassification.HSFLit

open Equiv

@[expose] def aff8 (u : (ZMod 8)ˣ) (b : ZMod 8) : Perm (ZMod 8) :=
  (Units.mulLeft u).trans (Equiv.addRight b)

@[simp] theorem aff8_apply (u : (ZMod 8)ˣ) (b v : ZMod 8) : aff8 u b v = u * v + b := rfl

theorem aff8_mul (u u' : (ZMod 8)ˣ) (b b' : ZMod 8) :
    aff8 u b * aff8 u' b' = aff8 (u * u') (b + u * b') := by
  ext v
  simp only [Perm.mul_apply, aff8_apply, Units.val_mul]
  ring

theorem aff8_one : aff8 1 0 = 1 := by
  ext v
  simp

theorem aff8_inv (u : (ZMod 8)ˣ) (b : ZMod 8) : (aff8 u b)⁻¹ = aff8 u⁻¹ (-(u⁻¹ * b)) := by
  rw [inv_eq_iff_mul_eq_one, aff8_mul, mul_inv_cancel, mul_neg, ← mul_assoc, Units.mul_inv,
    one_mul, add_neg_cancel, aff8_one]

theorem aff8_injective {u u' : (ZMod 8)ˣ} {b b' : ZMod 8} (h : aff8 u b = aff8 u' b') :
    u = u' ∧ b = b' := by
  have h0 := congrArg (fun g : Perm (ZMod 8) => g 0) h
  have h1 := congrArg (fun g : Perm (ZMod 8) => g 1) h
  simp only [aff8_apply, mul_zero, zero_add, mul_one] at h0 h1
  rw [h0] at h1
  exact ⟨Units.ext (add_right_cancel h1), h0⟩

@[expose] def H8 : Subgroup (Perm (ZMod 8)) where
  carrier := {g | ∃ u b, aff8 u b = g}
  one_mem' := ⟨1, 0, aff8_one⟩
  mul_mem' := by
    rintro _ _ ⟨u, b, rfl⟩ ⟨u', b', rfl⟩
    exact ⟨_, _, (aff8_mul u u' b b').symm⟩
  inv_mem' := by
    rintro _ ⟨u, b, rfl⟩
    exact ⟨_, _, (aff8_inv u b).symm⟩

theorem aff8_mem_H8 (u : (ZMod 8)ˣ) (b : ZMod 8) : aff8 u b ∈ H8 := ⟨u, b, rfl⟩

@[expose] def D16 : Subgroup (Perm (ZMod 8)) where
  carrier := {g | ∃ u b, (u = 1 ∨ u = -1) ∧ aff8 u b = g}
  one_mem' := ⟨1, 0, Or.inl rfl, aff8_one⟩
  mul_mem' := by
    rintro _ _ ⟨u, b, hu, rfl⟩ ⟨u', b', hu', rfl⟩
    refine ⟨_, _, ?_, (aff8_mul u u' b b').symm⟩
    rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl <;> simp
  inv_mem' := by
    rintro _ ⟨u, b, hu, rfl⟩
    refine ⟨_, _, ?_, (aff8_inv u b).symm⟩
    rcases hu with rfl | rfl <;> simp

@[expose] def R8 : Subgroup (Perm (ZMod 8)) where
  carrier := {g | ∃ u c, (u = 1 ∨ u = -1) ∧ aff8 u (2 * c) = g}
  one_mem' := ⟨1, 0, Or.inl rfl, by rw [mul_zero, aff8_one]⟩
  mul_mem' := by
    rintro _ _ ⟨u, c, hu, rfl⟩ ⟨u', c', hu', rfl⟩
    refine ⟨u * u', c + u * c', ?_, ?_⟩
    · rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl <;> simp
    · rw [aff8_mul]
      congr 1
      ring
  inv_mem' := by
    rintro _ ⟨u, c, hu, rfl⟩
    refine ⟨u⁻¹, -(u⁻¹ * c), ?_, ?_⟩
    · rcases hu with rfl | rfl <;> simp
    · rw [aff8_inv]
      congr 1
      ring

@[expose] def C8 : Subgroup (Perm (ZMod 8)) := Subgroup.zpowers (aff8 1 1)

theorem aff8_one_pow (n : ℕ) : aff8 1 1 ^ n = aff8 1 n := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, aff8_one]
  | succ n ih => rw [pow_succ, ih, aff8_mul, one_mul, Units.val_one, one_mul, Nat.cast_succ]

theorem aff8_one_zpow (n : ℤ) : aff8 1 1 ^ n = aff8 1 n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, aff8_one_pow, Int.cast_natCast]
  · rw [zpow_neg, zpow_natCast, aff8_one_pow, aff8_inv, inv_one, Units.val_one, one_mul,
      Int.cast_neg, Int.cast_natCast]

theorem mem_C8_iff {g : Perm (ZMod 8)} : g ∈ C8 ↔ ∃ b, aff8 1 b = g := by
  constructor
  · intro hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨n, (aff8_one_zpow n).symm⟩
  · rintro ⟨b, rfl⟩
    have : aff8 1 b = aff8 1 1 ^ b.val := by rw [aff8_one_pow, ZMod.natCast_zmod_val]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

instance : IsCyclic C8 := Subgroup.isCyclic_zpowers _

instance decidableMemH8 : DecidablePred (· ∈ H8) := fun _ =>
  decidable_of_iff (∃ u b, aff8 u b = _) Iff.rfl

instance decidableMemD16 : DecidablePred (· ∈ D16) := fun _ =>
  decidable_of_iff (∃ u b, (u = 1 ∨ u = -1) ∧ aff8 u b = _) Iff.rfl

instance decidableMemR8 : DecidablePred (· ∈ R8) := fun _ =>
  decidable_of_iff (∃ u c, (u = 1 ∨ u = -1) ∧ aff8 u (2 * c) = _) Iff.rfl

theorem units_mul_self_eight : ∀ u : (ZMod 8)ˣ, u * u = 1 := by decide

@[expose] def linF (g : Perm (ZMod 8)) : ZMod 8 := g 1 - g 0

theorem linF_aff8 (u : (ZMod 8)ˣ) (b : ZMod 8) : linF (aff8 u b) = u := by
  simp [linF]

theorem linF_mul_self_of_mem {g : Perm (ZMod 8)} (hg : g ∈ H8) : linF g * linF g = 1 := by
  obtain ⟨u, b, rfl⟩ := hg
  rw [linF_aff8, ← Units.val_mul, units_mul_self_eight, Units.val_one]

@[expose] def lin8 : H8 →* (ZMod 8)ˣ where
  toFun g := ⟨linF g, linF g, linF_mul_self_of_mem g.2, linF_mul_self_of_mem g.2⟩
  map_one' := by
    ext
    simp [linF]
  map_mul' g g' := by
    obtain ⟨_, u, b, rfl⟩ := g
    obtain ⟨_, u', b', rfl⟩ := g'
    ext
    change linF (aff8 u b * aff8 u' b') = linF (aff8 u b) * linF (aff8 u' b')
    rw [aff8_mul, linF_aff8, linF_aff8, linF_aff8, Units.val_mul]

theorem lin8_aff8 (u : (ZMod 8)ˣ) (b : ZMod 8) : lin8 ⟨aff8 u b, aff8_mem_H8 u b⟩ = u := by
  ext
  exact linF_aff8 u b

theorem lin8_eq_one_iff (g : H8) : lin8 g = 1 ↔ (g : Perm (ZMod 8)) ∈ C8 := by
  obtain ⟨_, u, b, rfl⟩ := g
  rw [lin8_aff8, mem_C8_iff]
  constructor
  · rintro rfl
    exact ⟨b, rfl⟩
  · rintro ⟨b', h⟩
    exact (aff8_injective h).1.symm

@[expose] def fbit8 (u : ZMod 8) : ZMod 2 := if u = 3 ∨ u = 5 then 1 else 0

@[expose] def dbit8 (b : ZMod 8) : ZMod 2 := (b.val : ZMod 2)

theorem type8_mul_aux : ∀ u u' : (ZMod 8)ˣ, ∀ b b' : ZMod 8,
    dbit8 (b + u * b') = dbit8 b + dbit8 b' ∧ fbit8 (u * u' : (ZMod 8)ˣ) = fbit8 u + fbit8 u' := by
  decide

@[expose] def type8 : H8 →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun g := Multiplicative.ofAdd (dbit8 ((g : Perm (ZMod 8)) 0), fbit8 (linF g))
  map_one' := by
    simp only [OneMemClass.coe_one, Perm.one_apply, linF, sub_zero]
    decide
  map_mul' g g' := by
    obtain ⟨_, u, b, rfl⟩ := g
    obtain ⟨_, u', b', rfl⟩ := g'
    change Multiplicative.ofAdd (dbit8 ((aff8 u b * aff8 u' b') 0),
      fbit8 (linF (aff8 u b * aff8 u' b'))) = _
    rw [aff8_mul, linF_aff8, aff8_apply, mul_zero, zero_add, ← ofAdd_add]
    simp only [linF_aff8, aff8_apply, mul_zero, zero_add]
    obtain ⟨h1, h2⟩ := type8_mul_aux u u' b b'
    rw [h1, h2]
    rfl

theorem type8_aff8 (u : (ZMod 8)ˣ) (b : ZMod 8) :
    type8 ⟨aff8 u b, aff8_mem_H8 u b⟩ = Multiplicative.ofAdd (dbit8 b, fbit8 u) := by
  change Multiplicative.ofAdd (dbit8 (aff8 u b 0), fbit8 (linF (aff8 u b))) = _
  rw [linF_aff8, aff8_apply, mul_zero, zero_add]

theorem card_units_zmod_eight : Nat.card (ZMod 8)ˣ = 4 := by
  rw [Nat.card_eq_fintype_card]
  rfl

abbrev x8 : Perm (ZMod 8) := aff8 1 2

abbrev y8 : Perm (ZMod 8) := aff8 (-1) 0

abbrev z8 : Perm (ZMod 8) := aff8 1 4

abbrev u5 : (ZMod 8)ˣ := ⟨5, 5, rfl, rfl⟩

abbrev u3 : (ZMod 8)ˣ := ⟨3, 3, rfl, rfl⟩

abbrev k8 : Perm (ZMod 8) := aff8 u5 0

abbrev d8 : Perm (ZMod 8) := aff8 (-1) 1

end CFSG.ComponentClassification.HSFLit

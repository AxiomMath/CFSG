module

import CFSG.Certificates.Kernel.GMS78RuP.Basic
public import Certificates.Data.GMS78RuSModelData
public import Certificates.Data.Kernel.GMS78RuS
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.GMS.S17

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

theorem neStrictB_eq (y : Nat) (k : Nat → Bool) : neStrictB y k = k y := by
  cases y <;> rfl

theorem neLen_eq {α : Type} (l : List α) : neLen l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change strictN (neLen l) Nat.succ = _
    rw [P117.strictN_eq, ih]
    rfl

theorem neGet_eq {α : Type} (d : α) (l : List α) (k : Nat) : neGet d l k = l.getD k d := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change neGet d l k = _
      rw [ih, List.getD_cons_succ]

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [P117.andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h2 i h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem fget_eq' (X i w : Nat) : fget X i w = X / 2 ^ (i * w) % 2 ^ w := by
  have h1 : maskN w = 2 ^ w - 1 := by simp [maskN, pw2, Nat.shiftLeft_eq]
  change (X >>> (i * w)) &&& maskN w = _
  rw [h1, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem getD_eq' {α : Type} (l : List α) (d : α) {n : Nat} (h : n < l.length) :
    l.getD n d = l[n] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem neAllL_iff {α : Type} {p : α → Bool} {l : List α} :
    neAllL p l = true ↔ ∀ x ∈ l, p x = true := by
  rw [P117.neAllL_eq, List.all_eq_true]

theorem sZipAll_iff (g : Nat → Nat → Bool) : ∀ (U K : List Nat),
    sZipAll g U K = true ↔ ∀ i < U.length, g (U.getD i 0) (K.getD i 0) = true
  | [], K => ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | u :: U, K => by
    have e : sZipAll g (u :: U) K = andB (g u (K.getD 0 0)) (sZipAll g U K.tail) := by
      cases K with
      | nil => rfl
      | cons a K => rfl
    rw [e, P117.andB_iff, sZipAll_iff g U K.tail]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | zero => exact h1
      | succ i =>
        have := h2 i (by simpa using hi)
        cases K with
        | nil => simpa using this
        | cons a K => simpa using this
    · intro h
      refine ⟨h 0 (by simp), fun i hi => ?_⟩
      have := h (i + 1) (by simpa using hi)
      cases K with
      | nil => simpa using this
      | cons a K => simpa using this

theorem sAllPairs_iff (f : Nat → Nat → Nat → Nat → Bool) (U K : List Nat) :
    sAllPairs f U K = true ↔ ∀ i < U.length, ∀ j < U.length,
      f (U.getD i 0) (K.getD i 0) (U.getD j 0) (K.getD j 0) = true := by
  unfold sAllPairs
  simp only [sZipAll_iff]

end CFSG.KC.GMS.S17

end

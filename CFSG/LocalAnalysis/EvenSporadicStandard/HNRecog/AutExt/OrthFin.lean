module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm Finset

abbrev Fv5 : Type := Fin 5 → ZMod 2

@[expose] def fv5Act (g : Perm (Fin 5)) (e : Fv5) : Fv5 := fun i => e (g⁻¹ i)

@[expose] def Fv5Even (e : Fv5) : Prop := ∑ i, e i = 0

@[expose] def fv5One : Fv5 := fun _ => 1

instance (e : Fv5) : Decidable (Fv5Even e) := by
  unfold Fv5Even; infer_instance

theorem fv5Act_even {g : Perm (Fin 5)} {e : Fv5} (h : Fv5Even e) : Fv5Even (fv5Act g e) := by
  unfold Fv5Even at h ⊢
  simpa [fv5Act] using (Equiv.sum_comp g⁻¹ e).trans h

theorem fv5Act_one_vec (g : Perm (Fin 5)) : fv5Act g fv5One = fv5One := by
  funext i; simp [fv5Act, fv5One]

theorem fv5Even_add {e f : Fv5} (he : Fv5Even e) (hf : Fv5Even f) : Fv5Even (e + f) := by
  unfold Fv5Even at *
  simp [Finset.sum_add_distrib, he, hf]

theorem fv5_add_self (e : Fv5) : e + e = 0 := by
  funext i
  simp [CharTwo.add_self_eq_zero]

theorem trans5 : ∀ i j : Fin 5, ∃ g : Perm (Fin 5), sign g = 1 ∧ g i = j := by
  decide +kernel

theorem stab_gen5 : ∀ g : Perm (Fin 5), sign g = 1 → g 0 = 0 →
    ∃ a b : Perm (Fin 5), sign a = 1 ∧ sign b = 1 ∧ a 0 = 0 ∧ b 0 = 0 ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      g = a * b := by
  decide +kernel

@[expose] def Fv5Fixed (g : Perm (Fin 5)) (e : Fv5) : Prop := fv5Act g e = e

instance (g : Perm (Fin 5)) (e : Fv5) : Decidable (Fv5Fixed g e) := by
  unfold Fv5Fixed fv5Act; infer_instance

@[expose] def Fv5FixAll (e c : Fv5) : Prop :=
  ∀ g : Perm (Fin 5), sign g = 1 → Fv5Fixed g e → Fv5Fixed g c

instance (e c : Fv5) : Decidable (Fv5FixAll e c) := by
  unfold Fv5FixAll; infer_instance

@[expose] def Fv5FixCase (e : Fv5) : Prop :=
  ∀ c : Fv5, Fv5Even c → Fv5FixAll e c → c = 0 ∨ c = e

instance (e : Fv5) : Decidable (Fv5FixCase e) := by
  unfold Fv5FixCase; infer_instance

theorem faithful5 : ∀ g : Perm (Fin 5), sign g = 1 →
    (∀ e : Fv5, Fv5Even e → fv5Act g e = e) → g = 1 := by
  unfold Fv5Even fv5Act
  decide +kernel

theorem fix5 : ∀ e : Fv5, Fv5Even e → e ≠ 0 → ∀ c : Fv5, Fv5Even c →
    (∀ g : Perm (Fin 5), sign g = 1 → fv5Act g e = e → fv5Act g c = c) → c = 0 ∨ c = e := by
  have h : ∀ e : Fv5, Fv5Even e → e ≠ 0 → Fv5FixCase e := by decide +kernel
  intro e he hne c hc hfix
  exact h e he hne c hc hfix

theorem card_fv5Even : (univ.filter fun e : Fv5 => Fv5Even e).card = 16 := by
  unfold Fv5Even
  decide +kernel

end CFSG.EvenSporadicStandard.HNRecog.Section4

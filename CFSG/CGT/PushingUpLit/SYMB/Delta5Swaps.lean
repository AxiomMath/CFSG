module

public import CFSG.Quasithin.Background.G6Natural

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Quasithin

namespace Delta5Swaps

@[expose] def stab (w : G6.coreMod 5) : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | G6.coreAct 5 σ w = w}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show G6.coreAct 5 (a * b) w = w
    rw [map_mul, MulAut.mul_apply]
    have hb' : G6.coreAct 5 b w = w := hb
    have ha' : G6.coreAct 5 a w = w := ha
    rw [hb', ha']
  inv_mem' := fun {a} ha => by
    show G6.coreAct 5 a⁻¹ w = w
    have ha' : G6.coreAct 5 a w = w := ha
    calc G6.coreAct 5 a⁻¹ w = G6.coreAct 5 a⁻¹ (G6.coreAct 5 a w) := by rw [ha']
      _ = w := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

@[expose] def Fixed (P : Subgroup (Equiv.Perm (Fin 5))) : Subgroup (G6.coreMod 5) where
  carrier := {w | P ≤ stab w}
  one_mem' := by
    intro σ _
    show G6.coreAct 5 σ 1 = 1
    simp
  mul_mem' := fun {a b} ha hb σ hσ => by
    show G6.coreAct 5 σ (a * b) = a * b
    rw [map_mul]
    have ha' : G6.coreAct 5 σ a = a := ha hσ
    have hb' : G6.coreAct 5 σ b = b := hb hσ
    rw [ha', hb']
  inv_mem' := fun {a} ha σ hσ => by
    show G6.coreAct 5 σ a⁻¹ = a⁻¹
    rw [map_inv]
    have ha' : G6.coreAct 5 σ a = a := ha hσ
    rw [ha']

theorem mem_Fixed {P : Subgroup (Equiv.Perm (Fin 5))} {w : G6.coreMod 5} :
    w ∈ Fixed P ↔ ∀ σ ∈ P, G6.coreAct 5 σ w = w := Iff.rfl

theorem Fixed_zpowers {σ : Equiv.Perm (Fin 5)} {w : G6.coreMod 5} :
    w ∈ Fixed (Subgroup.zpowers σ) ↔ G6.coreAct 5 σ w = w := by
  rw [mem_Fixed]
  constructor
  · intro h
    exact h σ (Subgroup.mem_zpowers σ)
  · intro h τ hτ
    have : Subgroup.zpowers σ ≤ stab w := (Subgroup.zpowers_le).2 h
    exact this hτ

theorem Fixed_sup {P Q : Subgroup (Equiv.Perm (Fin 5))} : Fixed (P ⊔ Q) = Fixed P ⊓ Fixed Q := by
  ext w
  rw [Subgroup.mem_inf]
  show P ⊔ Q ≤ stab w ↔ P ≤ stab w ∧ Q ≤ stab w
  exact sup_le_iff

theorem Fixed_bot : Fixed ⊥ = ⊤ := by
  refine eq_top_iff.2 fun w _ σ hσ => ?_
  rw [Subgroup.mem_bot.1 hσ]
  simp

section Finite

local instance instDecidablePredMemCore : DecidablePred (· ∈ G6.coreMod 5) :=
  fun x => decidable_of_iff (∑ i, Multiplicative.toAdd x i = 0) G6.mem_coreMod.symm

open Equiv in
theorem fix_card_one : ∀ a b : Fin 5, a ≠ b →
    (Finset.univ.filter (fun w : G6.coreMod 5 => G6.coreAct 5 (swap a b) w = w)).card = 8 := by
  set_option synthInstance.maxSize 2000 in decide +kernel

open Equiv in
theorem fix_card_two : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    (Finset.univ.filter (fun w : G6.coreMod 5 => G6.coreAct 5 (swap a b) w = w ∧
      G6.coreAct 5 (swap c d) w = w)).card = 4 := by
  set_option synthInstance.maxSize 2000 in decide +kernel

open Equiv in
theorem fix_gen : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    ∀ w : G6.coreMod 5, ∃ w₁ w₂ : G6.coreMod 5, G6.coreAct 5 (swap a b) w₁ = w₁ ∧
      G6.coreAct 5 (swap c d) w₂ = w₂ ∧ w = w₁ * w₂ := by
  set_option synthInstance.maxSize 2000 in decide +kernel

open Equiv in
theorem fix_prod : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    ∀ w : G6.coreMod 5, G6.coreAct 5 (swap a b * swap c d) w = w ↔
      (G6.coreAct 5 (swap a b) w = w ∧ G6.coreAct 5 (swap c d) w = w) := by
  set_option synthInstance.maxSize 2000 in decide +kernel

theorem card_core : Nat.card (G6.coreMod 5) = 16 := by
  classical
  rw [Nat.card_eq_fintype_card]
  set_option synthInstance.maxSize 2000 in decide +kernel

theorem Fixed_anti {P Q : Subgroup (Equiv.Perm (Fin 5))} (h : P ≤ Q) : Fixed Q ≤ Fixed P :=
  fun _ hw _ hσ => hw (h hσ)

open Equiv in
theorem card_Fixed_swap {a b : Fin 5} (hab : a ≠ b) :
    Nat.card ↥(Fixed (Subgroup.zpowers (swap a b))) = 8 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun w => (Fixed_zpowers (σ := swap a b) (w := w))),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact fix_card_one a b hab

open Equiv in
theorem card_Fixed_pair {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    Nat.card ↥(Fixed (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d))) = 4 := by
  classical
  have : ∀ w : G6.coreMod 5, w ∈ Fixed (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) ↔
      (G6.coreAct 5 (swap a b) w = w ∧ G6.coreAct 5 (swap c d) w = w) := by
    intro w
    rw [Fixed_sup, Subgroup.mem_inf, Fixed_zpowers, Fixed_zpowers]
  rw [Nat.card_congr (Equiv.subtypeEquivRight this), Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact fix_card_two a b c d hab hcd hac had hbc hbd

open Equiv in
theorem card_Fixed_prod {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    Nat.card ↥(Fixed (Subgroup.zpowers (swap a b * swap c d))) = 4 := by
  classical
  have : ∀ w : G6.coreMod 5, w ∈ Fixed (Subgroup.zpowers (swap a b * swap c d)) ↔
      (G6.coreAct 5 (swap a b) w = w ∧ G6.coreAct 5 (swap c d) w = w) := by
    intro w
    rw [Fixed_zpowers]
    exact fix_prod a b c d hab hcd hac had hbc hbd w
  rw [Nat.card_congr (Equiv.subtypeEquivRight this), Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact fix_card_two a b c d hab hcd hac had hbc hbd

theorem card_Fixed_bot : Nat.card ↥(Fixed ⊥) = 16 := by
  rw [Fixed_bot]
  have : Nat.card ↥(⊤ : Subgroup (G6.coreMod 5)) = Nat.card (G6.coreMod 5) :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [this, card_core]

open Equiv in
theorem sup_Fixed_eq_top {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    Fixed (Subgroup.zpowers (swap a b)) ⊔ Fixed (Subgroup.zpowers (swap c d)) = ⊤ := by
  refine eq_top_iff.2 fun w _ => ?_
  obtain ⟨w₁, w₂, h₁, h₂, rfl⟩ := fix_gen a b c d hab hcd hac had hbc hbd w
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Fixed_zpowers.2 h₁))
    (Subgroup.mem_sup_right (Fixed_zpowers.2 h₂))

end Finite

end Delta5Swaps

end CFSG.CGT.PushingUpLit.SYMB

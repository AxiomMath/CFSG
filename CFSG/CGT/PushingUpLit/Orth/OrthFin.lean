module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.CGT.PushingUpLit.Orth

open Equiv
open scoped commutatorElement

abbrev Vec5 : Type := Fin 5 → ZMod 2

@[expose] def permAct (σ : Perm (Fin 5)) (v : Vec5) : Vec5 := fun i => v (σ.symm i)

theorem permAct_one (v : Vec5) : permAct 1 v = v := rfl

theorem permAct_mul (σ ρ : Perm (Fin 5)) (v : Vec5) :
    permAct (σ * ρ) v = permAct σ (permAct ρ v) := rfl

theorem permAct_inv_permAct (σ : Perm (Fin 5)) (v : Vec5) : permAct σ⁻¹ (permAct σ v) = v := by
  rw [← permAct_mul, inv_mul_cancel, permAct_one]

@[expose] def wt (v : Vec5) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

@[expose] def Rigid (v : Vec5) : Prop := v ≠ 0 ∧ (wt v = 1 ∨ wt v = 4 ∨ wt v = 5)

instance (v : Vec5) : Decidable (Rigid v) := by unfold Rigid; infer_instance

@[expose] def canon (k : ℕ) : Vec5 := fun i => if i.val < k then 1 else 0

theorem exists_perm_canon : ∀ v : Vec5, ∃ σ : Perm (Fin 5), permAct σ v = canon (wt v) := by
  decide +kernel

theorem exists_perm_of_wt_eq {v w : Vec5} (h : wt v = wt w) :
    ∃ σ : Perm (Fin 5), permAct σ v = w := by
  obtain ⟨σ, hσ⟩ := exists_perm_canon v
  obtain ⟨ρ, hρ⟩ := exists_perm_canon w
  refine ⟨ρ⁻¹ * σ, ?_⟩
  rw [permAct_mul, hσ, h, ← hρ, permAct_inv_permAct]

@[expose] def ones : Vec5 := fun _ => 1

@[expose] def z4 : Vec5 := ![1, 1, 1, 1, 0]

@[expose] def z1 : Vec5 := ![0, 0, 0, 0, 1]

@[expose] def v2 : Vec5 := ![1, 1, 0, 0, 0]

@[expose] def v3 : Vec5 := ![0, 0, 1, 1, 1]

theorem wt_ones : wt ones = 5 := by decide
theorem wt_z4 : wt z4 = 4 := by decide
theorem wt_z1 : wt z1 = 1 := by decide
theorem wt_v2 : wt v2 = 2 := by decide
theorem wt_v3 : wt v3 = 3 := by decide

theorem permAct_ones (σ : Perm (Fin 5)) : permAct σ ones = ones := rfl

theorem ones_ne_zero : ones ≠ 0 := by decide
theorem z4_ne_zero : z4 ≠ 0 := by decide
theorem z4_ne_z1 : z4 ≠ z1 := by decide
theorem rigid_ones : Rigid ones := by decide
theorem rigid_z4 : Rigid z4 := by decide
theorem rigid_z1 : Rigid z1 := by decide

theorem add_self_vec (v : Vec5) : v + v = 0 := by revert v; decide +kernel

theorem fixed_all (w : Vec5) (h : ∀ σ : Perm (Fin 5), permAct σ w = w) : w = 0 ∨ w = ones := by
  revert w; decide +kernel

@[expose] def isD8 (σ : Perm (Fin 5)) : Prop := σ 4 = 4 ∧ (σ 2).val = ((σ 0).val + 2) % 4

instance : DecidablePred isD8 := fun σ => by unfold isD8; infer_instance

theorem isD8_one : isD8 1 := by decide
theorem isD8_mul : ∀ σ ρ : Perm (Fin 5), isD8 σ → isD8 ρ → isD8 (σ * ρ) := by decide +kernel
theorem isD8_inv : ∀ σ : Perm (Fin 5), isD8 σ → isD8 σ⁻¹ := by decide +kernel

@[expose] def D8 : Subgroup (Perm (Fin 5)) where
  carrier := {σ | isD8 σ}
  mul_mem' := fun {a b} ha hb => isD8_mul a b ha hb
  one_mem' := isD8_one
  inv_mem' := fun {a} ha => isD8_inv a ha

theorem mem_D8 {σ : Perm (Fin 5)} : σ ∈ D8 ↔ isD8 σ :=
  ⟨fun h => h, fun h => h⟩

instance : DecidablePred (· ∈ D8) := fun σ => decidable_of_iff (isD8 σ) mem_D8.symm

theorem card_D8 : Nat.card D8 = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem isPGroup_D8 : IsPGroup 2 D8 := IsPGroup.of_card (n := 3) (by rw [card_D8]; norm_num)

theorem index_D8 : D8.index = 15 := by
  have h := D8.card_mul_index
  rw [card_D8, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
  norm_num [Nat.factorial] at h
  omega

theorem D8_fixed (w : Vec5) (h : ∀ σ : Perm (Fin 5), isD8 σ → permAct σ w = w) :
    w = 0 ∨ w = z4 ∨ w = z1 ∨ w = ones := by
  revert w; decide +kernel

theorem D8_normalizer (σ : Perm (Fin 5)) (h : ∀ d : Perm (Fin 5), isD8 d → isD8 (σ * d * σ⁻¹)) :
    isD8 σ := by
  revert σ; decide +kernel

theorem D8_fixes_z4 : ∀ σ : Perm (Fin 5), isD8 σ → permAct σ z4 = z4 := by decide +kernel
theorem D8_fixes_z1 : ∀ σ : Perm (Fin 5), isD8 σ → permAct σ z1 = z1 := by decide +kernel

@[expose] def isH2 (σ : Perm (Fin 5)) : Prop := (σ 0 = 0 ∨ σ 0 = 1) ∧ (σ 1 = 0 ∨ σ 1 = 1)

instance : DecidablePred isH2 := fun σ => by unfold isH2; infer_instance

theorem isH2_one : isH2 1 := by decide
theorem isH2_mul : ∀ σ ρ : Perm (Fin 5), isH2 σ → isH2 ρ → isH2 (σ * ρ) := by decide +kernel
theorem isH2_inv : ∀ σ : Perm (Fin 5), isH2 σ → isH2 σ⁻¹ := by decide +kernel

@[expose] def H2 : Subgroup (Perm (Fin 5)) where
  carrier := {σ | isH2 σ}
  mul_mem' := fun {a b} ha hb => isH2_mul a b ha hb
  one_mem' := isH2_one
  inv_mem' := fun {a} ha => isH2_inv a ha

theorem mem_H2 {σ : Perm (Fin 5)} : σ ∈ H2 ↔ isH2 σ :=
  ⟨fun h => h, fun h => h⟩

instance : DecidablePred (· ∈ H2) := fun σ => decidable_of_iff (isH2 σ) mem_H2.symm

@[expose] def tau : Perm (Fin 5) := Equiv.swap 0 1

theorem tau_mem_H2 : tau ∈ H2 := by decide +kernel

theorem tau_ne_one : tau ≠ 1 := by decide +kernel

theorem tau_mul_self : tau * tau = 1 := by decide +kernel

theorem permAct_v2 (σ : Perm (Fin 5)) : permAct σ v2 = v2 ↔ isH2 σ := by
  revert σ; decide +kernel

theorem permAct_v3 (σ : Perm (Fin 5)) : permAct σ v3 = v3 ↔ isH2 σ := by
  revert σ; decide +kernel

theorem normal2 (ρ : Perm (Fin 5)) (hρ : isH2 ρ)
    (h : ∀ σ : Perm (Fin 5), isH2 σ → ⁅σ, ρ⁆ ^ 4 = 1) : ρ = 1 ∨ ρ = tau := by
  revert ρ; decide +kernel

theorem mem_zpowers_tau {σ : Perm (Fin 5)} : σ ∈ Subgroup.zpowers tau ↔ σ = 1 ∨ σ = tau := by
  have h2 : tau ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact tau_mul_self
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
      rw [hj, zpow_mul, h2, one_zpow]
    · right
      obtain ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
      rw [hj, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem isPGroup_zpowers_tau : IsPGroup 2 (Subgroup.zpowers tau) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf tau = 2 := orderOf_eq_prime (by rw [pow_two]; exact tau_mul_self) tau_ne_one
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2]; norm_num)

theorem card_zpowers_tau : Nat.card (Subgroup.zpowers tau) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf tau = 2 := orderOf_eq_prime (by rw [pow_two]; exact tau_mul_self) tau_ne_one
  rw [Nat.card_zpowers, h2]

theorem permAct_tau_iff (v : Vec5) : permAct tau v = v ↔ v 0 = v 1 := by
  revert v; decide +kernel

theorem permAct_tau_add (v : Vec5) : permAct tau v + v = 0 ∨ permAct tau v + v = v2 := by
  revert v; decide +kernel

theorem permAct_tau_zero (v : Vec5) (h : v 0 = v 1) : permAct tau v = v :=
  (permAct_tau_iff v).2 h

@[expose] def stab (v : Vec5) : Subgroup (Perm (Fin 5)) where
  carrier := {σ | permAct σ v = v}
  mul_mem' := fun {a b} ha hb => by
    show permAct (a * b) v = v
    rw [permAct_mul]
    have hb' : permAct b v = v := hb
    have ha' : permAct a v = v := ha
    rw [hb', ha']
  one_mem' := rfl
  inv_mem' := fun {a} ha => by
    show permAct a⁻¹ v = v
    have ha' : permAct a v = v := ha
    conv_lhs => rw [← ha']
    exact permAct_inv_permAct a v

theorem mem_stab {σ : Perm (Fin 5)} {v : Vec5} : σ ∈ stab v ↔ permAct σ v = v :=
  ⟨fun h => h, fun h => h⟩

instance (v : Vec5) : DecidablePred (· ∈ stab v) := fun σ =>
  decidable_of_iff (permAct σ v = v) mem_stab.symm

theorem card_stab_wt2 : ∀ v : Vec5, wt v = 2 → Nat.card (stab v) = 12 := by
  intro v hv
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  revert v; decide +kernel

theorem card_stab_wt1 : ∀ v : Vec5, wt v = 1 → Nat.card (stab v) = 24 := by
  intro v hv
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  revert v; decide +kernel

theorem card_stab_wt4 : ∀ v : Vec5, wt v = 4 → Nat.card (stab v) = 24 := by
  intro v hv
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  revert v; decide +kernel

theorem eq_ones_of_wt_five : ∀ v : Vec5, wt v = 5 → v = ones := by decide +kernel

@[expose] def lam5 : List Vec5 :=
  [![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![1, 1, 1, 1, 0], ![1, 1, 1, 0, 1],
    ![1, 1, 0, 1, 1], ![1, 1, 1, 1, 1]]

@[expose] def nonrig5 : List Vec5 :=
  [![1, 1, 0, 0, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 0, 1], ![0, 0, 0, 1, 1], ![1, 1, 1, 0, 0],
    ![1, 1, 0, 1, 0], ![1, 1, 0, 0, 1], ![0, 0, 1, 1, 1]]

theorem rigid_of_mem_lam5 : ∀ v ∈ lam5, Rigid v := by decide +kernel

theorem mem_nonrig5 : ∀ v : Vec5, v 0 = v 1 → v ≠ 0 → ¬ Rigid v → v ∈ nonrig5 := by
  decide +kernel

@[expose] def good5 (x1 x2 x3 x4 : Vec5) : Prop :=
  x1 + x2 ≠ 0 ∧ x1 + x3 ≠ 0 ∧ x1 + x4 ≠ 0 ∧ x2 + x3 ≠ 0 ∧ x2 + x4 ≠ 0 ∧ x3 + x4 ≠ 0 ∧
  x1 + x2 + x3 ≠ 0 ∧ x1 + x2 + x4 ≠ 0 ∧ x1 + x3 + x4 ≠ 0 ∧ x2 + x3 + x4 ≠ 0 ∧
  x1 + x2 + x3 + x4 ≠ 0

instance (x1 x2 x3 x4 : Vec5) : Decidable (good5 x1 x2 x3 x4) := by unfold good5; infer_instance

@[expose] def hit5 (x1 x2 x3 x4 : Vec5) : Prop :=
  x3 + x4 ∈ lam5 ∨ x1 + x3 + x4 ∈ lam5 ∨ x2 + x3 + x4 ∈ lam5

instance (x1 x2 x3 x4 : Vec5) : Decidable (hit5 x1 x2 x3 x4) := by unfold hit5; infer_instance

theorem F1core : ∀ x1 ∈ nonrig5, ∀ x2 ∈ nonrig5, ∀ x3 ∈ nonrig5, ∀ x4 ∈ nonrig5,
    good5 x1 x2 x3 x4 → hit5 x1 x2 x3 x4 := by
  decide +kernel

@[expose] def p1 : Vec5 := ![1, 1, 1, 0, 0]
@[expose] def p2 : Vec5 := ![1, 1, 0, 1, 0]
@[expose] def p3 : Vec5 := ![1, 1, 0, 0, 1]
@[expose] def p4 : Vec5 := ![0, 0, 1, 1, 1]

theorem p_props : (wt p1 = 3 ∧ p1 0 = p1 1) ∧ (wt p2 = 3 ∧ p2 0 = p2 1) ∧
    (wt p3 = 3 ∧ p3 0 = p3 1) ∧ (wt p4 = 3 ∧ p4 0 = p4 1) := by decide +kernel

theorem eq_p_of_wt3 : ∀ u : Vec5, u 0 = u 1 → wt u = 3 → u = p1 ∨ u = p2 ∨ u = p3 ∨ u = p4 := by
  decide +kernel

theorem span_p : ∀ u : Vec5, u 0 = u 1 → ∃ a b c d : Bool,
    u = (if a then p1 else 0) + (if b then p2 else 0) + (if c then p3 else 0) +
      (if d then p4 else 0) := by
  decide +kernel

theorem eq_zero_of_wt_zero : ∀ v : Vec5, wt v = 0 → v = 0 := by decide +kernel

theorem wt_le_five : ∀ v : Vec5, wt v ≤ 5 := by decide +kernel

end CFSG.CGT.PushingUpLit.Orth

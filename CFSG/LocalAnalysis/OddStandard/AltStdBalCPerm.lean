module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.AltStdBal

open Equiv Equiv.Perm

section Swaps

variable {α : Type*} [DecidableEq α]

theorem disjoint_swap_mul_swap_sq {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (swap a b * swap c d) * (swap a b * swap c d) = 1 ∧ swap a b * swap c d ≠ 1 := by
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def, Perm.coe_one, id_eq]
    split_ifs <;> simp_all
  · intro h
    have := congrArg (fun f : Perm α => f a) h
    simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def, Perm.coe_one, id_eq] at this
    split_ifs at this <;> simp_all

theorem perm_conj_swap_mul_swap (σ : Perm α) (a b c d : α) :
    σ * (swap a b * swap c d) * σ⁻¹ = swap (σ a) (σ b) * swap (σ c) (σ d) := by
  rw [swap_apply_apply, swap_apply_apply]
  group

theorem commutator_three_cycle {σ : Perm α} (hσ : σ * σ = 1) {p q r s : α} (hp : σ p = q)
    (hr : σ r = s) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s)
    (hrs : r ≠ s) :
    σ * (swap p q * swap p r) * σ⁻¹ * (swap p q * swap p r)⁻¹ = swap p s * swap q r := by
  have hq : σ q = p := by
    have := congrArg (fun f : Perm α => f p) hσ
    simpa [hp] using this
  rw [perm_conj_swap_mul_swap, hp, hq, hr, mul_inv_rev, swap_inv, swap_inv]
  ext x
  simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem commutator_two_two {σ : Perm α} (hσ : σ * σ = 1) {p q r s : α} (hp : σ p = q)
    (hr : σ r = r) (hs : σ s = s) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) :
    σ * (swap p r * swap q s) * σ⁻¹ * (swap p r * swap q s)⁻¹ = swap p q * swap r s := by
  have hq : σ q = p := by
    have := congrArg (fun f : Perm α => f p) hσ
    simpa [hp] using this
  rw [perm_conj_swap_mul_swap, hp, hq, hr, hs, mul_inv_rev, swap_inv, swap_inv]
  ext x
  simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def]
  split_ifs <;> simp_all

end Swaps

section Main

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_even_commutator_involution (hα : 4 ≤ Fintype.card α) {σ : Perm α} (hσ1 : σ ≠ 1)
    (hσ2 : σ * σ = 1) :
    ∃ c : Perm α, sign c = 1 ∧
      (σ * c * σ⁻¹ * c⁻¹) * (σ * c * σ⁻¹ * c⁻¹) = 1 ∧ σ * c * σ⁻¹ * c⁻¹ ≠ 1 := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, σ p ≠ p := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Equiv.ext hcon)
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    simpa using congrArg (fun f : Perm α => f x) hσ2
  by_cases hA : ∃ r, r ≠ p ∧ r ≠ σ p ∧ σ r ≠ r
  · obtain ⟨r, hrp, hrq, hr⟩ := hA
    have hpq : p ≠ σ p := fun h => hp h.symm
    have hpr : p ≠ r := fun h => hrp h.symm
    have hps : p ≠ σ r := fun h => hrq (by rw [h, hσσ r])
    have hqr : σ p ≠ r := fun h => hrq h.symm
    have hqs : σ p ≠ σ r := fun h => hpr (σ.injective h)
    have hrs : r ≠ σ r := fun h => hr h.symm
    refine ⟨swap p (σ p) * swap p r, ?_, ?_⟩
    · rw [sign_mul, sign_swap hpq, sign_swap hpr]
      decide
    · rw [commutator_three_cycle hσ2 rfl rfl hpq hpr hps hqr hqs hrs]
      exact disjoint_swap_mul_swap_sq hps hqr hpq hpr (Ne.symm hqs) (Ne.symm hrs)
  · push Not at hA
    have hcard : 1 < ((Finset.univ : Finset α) \ {p, σ p}).card := by
      have h1 : ((Finset.univ : Finset α) \ {p, σ p}).card =
          Fintype.card α - ({p, σ p} : Finset α).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      have h2 : ({p, σ p} : Finset α).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨r, hrT, s, hsT, hrs⟩ := Finset.one_lt_card.1 hcard
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at hrT hsT
    have hr : σ r = r := hA r hrT.1 hrT.2
    have hs : σ s = s := hA s hsT.1 hsT.2
    have hpq : p ≠ σ p := fun h => hp h.symm
    have hpr : p ≠ r := fun h => hrT.1 h.symm
    have hps : p ≠ s := fun h => hsT.1 h.symm
    have hqr : σ p ≠ r := fun h => hrT.2 h.symm
    have hqs : σ p ≠ s := fun h => hsT.2 h.symm
    refine ⟨swap p r * swap (σ p) s, ?_, ?_⟩
    · rw [sign_mul, sign_swap hpr, sign_swap hqs]
      decide
    · rw [commutator_two_two hσ2 rfl hr hs hpq hpr hps hqr hqs hrs]
      exact disjoint_swap_mul_swap_sq hpq hrs hpr hps hqr hqs

end Main

end CFSG.OddStandard.AltStdBal

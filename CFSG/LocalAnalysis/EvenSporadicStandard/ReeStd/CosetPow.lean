module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup

theorem coset_fixed_of_small_index_pow {R : Type*} [Group R] [Finite R] {S : Subgroup R}
    (hidx : S.index ≤ 6) (σ : MulAut R) {a : ℕ} (hσ : σ ^ 7 ^ a = 1)
    (hS : S.map σ.toMonoidHom = S) (r : R) : σ r * r⁻¹ ∈ S := by
  classical
  have hSσ : ∀ x, x ∈ S → σ x ∈ S := fun x hx => by
    rw [← hS]
    exact Subgroup.mem_map_of_mem _ hx
  have : Fintype R := Fintype.ofFinite R
  let f : Function.End (R ⧸ S) := Quotient.map' σ fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have := hSσ _ hab
    simpa using this
  have hf1 : ∀ a : R, f (a : R ⧸ S) = ((σ a : R) : R ⧸ S) := fun a => rfl
  have hf : ∀ (n : ℕ) (a : R), (f ^ n) (a : R ⧸ S) = (((σ ^ n) a : R) : R ⧸ S) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      have : (f ^ (n + 1)) (a : R ⧸ S) = (f ^ n) (f (a : R ⧸ S)) := by
        rw [pow_succ]; rfl
      rw [this, hf1, ih, pow_succ, MulAut.mul_apply]
  have hf7 : f ^ 7 ^ a = 1 := by
    have : ∀ x : R ⧸ S, (f ^ 7 ^ a) x = x := by
      intro x
      induction x using Quotient.inductionOn' with
      | h b =>
        have := hf (7 ^ a) b
        rw [hσ] at this
        exact this
    exact funext this
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 7) (n := a) (α := R ⧸ S) hf7
  have hcard : Fintype.card (R ⧸ S) = S.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hle : Fintype.card f.fixedPoints ≤ Fintype.card (R ⧸ S) := Fintype.card_subtype_le _
  have heq : Fintype.card f.fixedPoints = Fintype.card (R ⧸ S) :=
    Nat.ModEq.eq_of_lt_of_lt hmod.symm (by omega) (by omega)
  have hall : ∀ x : R ⧸ S, f x = x := by
    intro x
    have h1 : (Set.toFinset f.fixedPoints).card = Fintype.card (R ⧸ S) := by
      rw [Set.toFinset_card, heq]
    have h2 := Finset.eq_univ_of_card _ h1
    have : x ∈ Set.toFinset f.fixedPoints := by rw [h2]; exact Finset.mem_univ x
    have h4 : x ∈ f.fixedPoints := Set.mem_toFinset.1 this
    exact h4
  have h3 := hall ((r⁻¹ : R) : R ⧸ S)
  rw [hf1, QuotientGroup.eq] at h3
  simpa using h3

end CFSG.EvenSporadicStandard.ReeStd

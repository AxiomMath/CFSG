module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec4I_fixed_of_pow_seven {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (h : V ≃ₗ[ZMod 3] V) (hh : h ^ 7 = 1)
    (p : Submodule (ZMod 3) V) (hp : ∀ x ∈ p, h x ∈ p)
    (hd : Module.finrank (ZMod 3) p ≤ 5) : ∀ x ∈ p, h x = x := by
  classical
  haveI : Finite ↥p := Module.finite_of_finite (ZMod 3)
  haveI : Fintype ↥p := Fintype.ofFinite ↥p
  let f : Function.End ↥p := fun u => ⟨h u, hp u u.2⟩
  have hiter : ∀ (m : ℕ) (u : ↥p), ((f^[m]) u : V) = (⇑h)^[m] (u : V) := by
    intro m
    induction m with
    | zero => intro u; rfl
    | succ m ih =>
        intro u
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        change h ((f^[m]) u : V) = h ((⇑h)^[m] (u : V))
        rw [ih u]
  have hf : f ^ 7 = 1 := by
    funext u
    apply Subtype.ext
    rw [congr_fun (hom_coe_pow (fun g : Function.End ↥p => g) rfl (fun _ _ => rfl) f 7) u]
    show (f^[7] u : V) = (u : V)
    rw [hiter 7 u]
    show (⇑h)^[7] (u : V) = (u : V)
    rw [← LinearEquiv.pow_apply h 7 (u : V), hh]
    rfl
  let q : Submodule (ZMod 3) V := p ⊓ LinearMap.ker (h.toLinearMap - 1)
  have hq_le : q ≤ p := inf_le_left
  have hmem : ∀ x : ↥p, x ∈ Function.fixedPoints f ↔
      (x : V) ∈ LinearMap.ker (h.toLinearMap - 1) := by
    intro x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · intro hfix
      have h' : f x = x := hfix
      exact congrArg Subtype.val h'
    · intro hx
      show f x = x
      exact Subtype.ext hx
  let e : Function.fixedPoints f ≃ ↥q :=
    { toFun := fun x => ⟨(x.1 : V), Submodule.mem_inf.2 ⟨x.1.2, (hmem x.1).1 x.2⟩⟩
      invFun := fun y => ⟨⟨y.1, (Submodule.mem_inf.1 y.2).1⟩,
        (hmem ⟨y.1, (Submodule.mem_inf.1 y.2).1⟩).2 (Submodule.mem_inf.1 y.2).2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  haveI : Finite ↥q := Module.finite_of_finite (ZMod 3)
  haveI : Fintype ↥q := Fintype.ofFinite ↥q
  have hfix : Nat.card (Function.fixedPoints f) = Nat.card ↥q := Nat.card_congr e
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have h1 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 7) (n := 1)
    (by simpa using hf)
  have hmod1 : Nat.card ↥p ≡ Nat.card ↥q [MOD 7] := by
    rw [← hfix, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact h1
  have hcardp : Nat.card ↥p = 3 ^ Module.finrank (ZMod 3) p := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3), ZMod.card]
  have hcardq : Nat.card ↥q = 3 ^ Module.finrank (ZMod 3) q := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3), ZMod.card]
  have hmod : 3 ^ Module.finrank (ZMod 3) p ≡ 3 ^ Module.finrank (ZMod 3) q [MOD 7] := by
    rw [← hcardp, ← hcardq]
    exact hmod1
  have he_le_d : Module.finrank (ZMod 3) q ≤ Module.finrank (ZMod 3) p :=
    Submodule.finrank_mono hq_le
  have key : ∀ d e : Fin 6, 3 ^ (d : ℕ) % 7 = 3 ^ (e : ℕ) % 7 → d = e := by decide
  have hnum : ∀ d e : ℕ, d ≤ 5 → e ≤ d → 3 ^ d % 7 = 3 ^ e % 7 → e = d := by
    intro d e hd5 hed hde
    have hd6 : d < 6 := lt_of_le_of_lt hd5 (by decide)
    have he6 : e < 6 := lt_of_le_of_lt (le_trans hed hd5) (by decide)
    have h' := key ⟨d, hd6⟩ ⟨e, he6⟩ hde
    exact (congrArg Fin.val h').symm
  have heq : Module.finrank (ZMod 3) q = Module.finrank (ZMod 3) p :=
    hnum _ _ hd he_le_d hmod
  have hqp : q = p := Submodule.eq_of_le_of_finrank_eq hq_le heq
  intro x hx
  have hxq : x ∈ q := by rw [hqp]; exact hx
  have hker : x ∈ LinearMap.ker (h.toLinearMap - 1) := (Submodule.mem_inf.mp hxq).2
  have hx' : h.toLinearMap x = x := by
    simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using
      (LinearMap.mem_ker.mp hker)
  simpa using hx'

end CFSG.OddStandard.SmallF3.Omega

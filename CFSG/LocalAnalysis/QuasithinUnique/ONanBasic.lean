module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.ONan

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_add_self (x y : V) : x + y + y = x := by
  rw [add_assoc, ZModModule.add_self, add_zero]

theorem add_self_add (x y : V) : x + (x + y) = y := by
  rw [← add_assoc, ZModModule.add_self, zero_add]

theorem add_eq_zero_iff_eq (x y : V) : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self]

theorem add_ne_zero_iff_ne (x y : V) : x + y ≠ 0 ↔ x ≠ y :=
  not_congr (add_eq_zero_iff_eq x y)

theorem zmod_smul_eq (c : ZMod 2) (x : V) : c • x = 0 ∨ c • x = x := by
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc c with rfl | rfl
  · left; exact zero_smul _ _
  · right; exact one_smul _ _

def submoduleOfAdd (S : Set V) (h0 : (0 : V) ∈ S) (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) :
    Submodule (ZMod 2) V where
  carrier := S
  zero_mem' := h0
  add_mem' := fun hx hy => hadd _ hx _ hy
  smul_mem' := fun c x hx => by
    rcases zmod_smul_eq c x with h | h
    · rw [h]; exact h0
    · rw [h]; exact hx

@[simp] theorem mem_submoduleOfAdd (S : Set V) (h0 : (0 : V) ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (x : V) :
    x ∈ submoduleOfAdd S h0 hadd ↔ x ∈ S := Iff.rfl

structure Setting (X R : Subgroup (V ≃ₗ[ZMod 2] V)) (A C : Submodule (ZMod 2) V) : Prop where
  le : R ≤ X
  isCompl : IsCompl A C
  preserves : ∀ r ∈ R, ∀ a ∈ A, r a ∈ A
  fixes : ∀ r ∈ R, ∀ c ∈ C, r c = c
  trans : ∀ a ∈ A, ∀ b ∈ A, a ≠ 0 → b ≠ 0 → ∃ r ∈ R, r a = b

variable {X R : Subgroup (V ≃ₗ[ZMod 2] V)} {A C : Submodule (ZMod 2) V}

theorem Setting.decomp (S : Setting X R A C) (v : V) : ∃ a ∈ A, ∃ e ∈ C, a + e = v := by
  have : v ∈ A ⊔ C := by rw [S.isCompl.sup_eq_top]; exact Submodule.mem_top
  exact Submodule.mem_sup.mp this

theorem Setting.eq_zero_of_mem (S : Setting X R A C) {x : V} (hA : x ∈ A) (hC : x ∈ C) :
    x = 0 :=
  Submodule.disjoint_def.mp S.isCompl.disjoint x hA hC

theorem Setting.add_inj (S : Setting X R A C) {a a' e e' : V} (ha : a ∈ A) (ha' : a' ∈ A)
    (he : e ∈ C) (he' : e' ∈ C) (h : a + e = a' + e') : a = a' ∧ e = e' := by
  have h1 : a - a' = e' - e := by
    rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
  have h2 : a - a' = 0 :=
    S.eq_zero_of_mem (A.sub_mem ha ha') (by rw [h1]; exact C.sub_mem he' he)
  have h3 : a = a' := sub_eq_zero.mp h2
  subst h3
  exact ⟨rfl, add_left_cancel h⟩

variable [Finite V]

theorem natCard_submodule (W : Submodule (ZMod 2) V) :
    Nat.card W = 2 ^ finrank (ZMod 2) W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem natCard_space : Nat.card V = 2 ^ finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem ncard_submodule (W : Submodule (ZMod 2) V) :
    (W : Set V).ncard = 2 ^ finrank (ZMod 2) W := by
  rw [← Nat.card_coe_set_eq]
  exact natCard_submodule W

theorem exists_mem_ne_two (W : Submodule (ZMod 2) V) (hW : 2 ≤ finrank (ZMod 2) W) (a b : V) :
    ∃ x ∈ W, x ≠ a ∧ x ≠ b := by
  have h1 : ({a, b} : Set V).ncard < (W : Set V).ncard := by
    have h2 : ({a, b} : Set V).ncard ≤ 2 := by
      refine (Set.ncard_insert_le a {b}).trans ?_
      rw [Set.ncard_singleton]
    have h3 : 4 ≤ (W : Set V).ncard := by
      rw [ncard_submodule]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ finrank (ZMod 2) W := Nat.pow_le_pow_right (by norm_num) hW
    omega
  obtain ⟨x, hxW, hx⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h1
  refine ⟨x, hxW, ?_, ?_⟩
  · intro h; exact hx (Or.inl h)
  · intro h; exact hx (Or.inr h)

end CFSG.QuasithinUnique.ONan

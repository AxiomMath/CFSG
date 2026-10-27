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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.A5.Kc3L5

open Matrix

abbrev W : Type := Fin 5 → ZMod 2

abbrev Gl : Type := GL (Fin 5) (ZMod 2)

theorem card_W : Nat.card W = 32 := by
  rw [Nat.card_fun]
  simp

@[expose] def act (g : Gl) (w : W) : W := (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w

theorem act_mul (g h : Gl) (w : W) : act (g * h) w = act g (act h w) := by
  simp [act]

theorem act_one (w : W) : act 1 w = w := by simp [act]

theorem act_add (g : Gl) (a b : W) : act g (a + b) = act g a + act g b := by
  simp [act, Matrix.mulVec_add]

theorem act_zero (g : Gl) : act g 0 = 0 := by simp [act]

theorem act_neg (g : Gl) (a : W) : act g (-a) = -act g a := by
  have h0 : -a + a = 0 := neg_add_cancel a
  have h : act g (-a) + act g a = 0 := by rw [← act_add, h0, act_zero]
  exact eq_neg_of_add_eq_zero_left h

theorem eq_one_of_act_eq (g : Gl) (h : ∀ w : W, act g w = w) : g = 1 := by
  ext i j
  have h2 : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ (Pi.single j 1) = Pi.single j 1 := h _
  rw [Matrix.mulVec_single_one] at h2
  have := congrFun h2 i
  simpa [Pi.single_apply, Matrix.one_apply] using this

@[expose] def fixedAdd (S : Set Gl) : AddSubgroup W where
  carrier := {w | ∀ g ∈ S, act g w = w}
  add_mem' := by
    intro a b ha hb g hg
    rw [act_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => act_zero g
  neg_mem' := by
    intro a ha g hg
    exact (act_neg g a).trans (congrArg Neg.neg (ha g hg))

theorem card_dvd_W (A : AddSubgroup W) : Nat.card A ∣ 32 := by
  have := AddSubgroup.card_addSubgroup_dvd_card A
  rwa [card_W] at this

theorem card_eq_pow (A : AddSubgroup W) : ∃ k : ℕ, k ≤ 5 ∧ Nat.card A = 2 ^ k := by
  have h := card_dvd_W A
  rw [show (32 : ℕ) = 2 ^ 5 by norm_num] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).1 h

@[expose, instance_reducible] def actOn (P : Subgroup Gl) (C : AddSubgroup W)
    (h : ∀ a ∈ P, ∀ c ∈ C, act a c ∈ C) : MulAction P C where
  smul a c := ⟨act (a : Gl) (c : W), h a a.2 c c.2⟩
  one_smul _ := Subtype.ext (act_one _)
  mul_smul _ _ _ := Subtype.ext (act_mul _ _ _)

theorem card_modEq_fixed {p : ℕ} [Fact p.Prime] (P : Subgroup Gl) (hP : IsPGroup p P)
    (A : AddSubgroup W) (hA : ∀ a ∈ P, ∀ c ∈ A, act a c ∈ A) :
    Nat.card A ≡ Nat.card ↥(A ⊓ fixedAdd (P : Set Gl)) [MOD p] := by
  let _ : MulAction P A := actOn P A hA
  have h := hP.card_modEq_card_fixedPoints A
  have heq : Nat.card (MulAction.fixedPoints P A) = Nat.card ↥(A ⊓ fixedAdd (P : Set Gl)) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨(c.1 : W), AddSubgroup.mem_inf.2 ⟨c.1.2, fun g hg => ?_⟩⟩
        invFun := fun w => ⟨⟨(w : W), (AddSubgroup.mem_inf.1 w.2).1⟩, fun a => ?_⟩
        left_inv := fun c => rfl
        right_inv := fun w => rfl }
    · have := c.2 ⟨g, hg⟩
      exact congrArg Subtype.val this
    · exact Subtype.ext ((AddSubgroup.mem_inf.1 w.2).2 a a.2)
  rw [heq] at h
  exact h

theorem num_two_or_thirty_two {n : ℕ} (hk : ∃ k : ℕ, k ≤ 5 ∧ n = 2 ^ k) (h : n ≡ 2 [MOD 5]) :
    n = 2 ∨ n = 32 := by
  obtain ⟨k, hk, rfl⟩ := hk
  interval_cases k <;> simp [Nat.ModEq] at h ⊢

theorem card_fix_five {x : Gl} (hx : orderOf x = 5) :
    Nat.card (fixedAdd ((Subgroup.zpowers x : Subgroup Gl) : Set Gl)) = 2 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set A : Subgroup Gl := Subgroup.zpowers x with hA
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by rw [hA, Nat.card_zpowers, hx]; norm_num)
  have hmod := card_modEq_fixed (p := 5) A hAp ⊤ (fun _ _ _ _ => AddSubgroup.mem_top _)
  rw [AddSubgroup.card_top, card_W, top_inf_eq] at hmod
  have hdvd := card_dvd_W (fixedAdd (A : Set Gl))
  have h2 : Nat.card (fixedAdd (A : Set Gl)) ≡ 2 [MOD 5] := by
    have : (32 : ℕ) ≡ 2 [MOD 5] := by decide
    exact hmod.symm.trans this
  have hle : Nat.card (fixedAdd (A : Set Gl)) ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : Nat.card (fixedAdd (A : Set Gl)) = 2 ∨ Nat.card (fixedAdd (A : Set Gl)) = 32 :=
    num_two_or_thirty_two (card_eq_pow _) h2
  rcases hcases with h | h
  · exact h
  · exfalso
    have htop : fixedAdd (A : Set Gl) = ⊤ := by
      rw [← AddSubgroup.card_eq_iff_eq_top, h, card_W]
    have hx1 : x = 1 := by
      refine eq_one_of_act_eq x fun v => ?_
      have hv : v ∈ fixedAdd (A : Set Gl) := by
        rw [htop]; trivial
      exact hv x (Subgroup.mem_zpowers x)
    rw [hx1, orderOf_one] at hx
    omega

end CFSG.QuasithinUnique.A5.Kc3L5

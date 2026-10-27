module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open scoped IsMulCommutative

theorem finite_and_card_closure_range_le {G : Type*} [Group G] {n : ℕ} (e : Fin n → G)
    (hsq : ∀ i, e i * e i = 1) (hcomm : ∀ i j, e i * e j = e j * e i) :
    Finite (Subgroup.closure (Set.range e)) ∧
      Nat.card (Subgroup.closure (Set.range e)) ≤ 2 ^ n := by
  classical
  let C : Subgroup G := Subgroup.closure (Set.range e)
  have hpair : (Set.range e).Pairwise Commute := by
    rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ _
    exact hcomm i j
  haveI hCcomm : IsMulCommutative C := Subgroup.isMulCommutative_closure hpair
  let ec : Fin n → C := fun i => ⟨e i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  have hec : ∀ i, ec i * ec i = 1 := fun i => Subtype.ext (by simpa using hsq i)
  let F : (Fin n → Bool) → C := fun b => ∏ i : Fin n, if b i then ec i else 1
  have hFmul : ∀ a b : Fin n → Bool, F a * F b = F (fun i => Bool.xor (a i) (b i)) := by
    intro a b
    show (∏ i : Fin n, (if a i then ec i else 1)) * (∏ i : Fin n, (if b i then ec i else 1))
      = ∏ i : Fin n, (if Bool.xor (a i) (b i) then ec i else 1)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases h : a i <;> cases h' : b i <;> simp [h, h', hec i]
  let Fg : (Fin n → Bool) → G := fun b => (F b : G)
  have hFg_mul : ∀ a b : Fin n → Bool, Fg a * Fg b = Fg (fun i => Bool.xor (a i) (b i)) :=
    fun a b => congrArg (fun x : C => (x : G)) (hFmul a b)
  have hFg_inv : ∀ a : Fin n → Bool, (Fg a)⁻¹ = Fg a := by
    intro a
    have h : Fg a * Fg a = 1 := by
      rw [hFg_mul a a]
      have : (fun i : Fin n => Bool.xor (a i) (a i)) = fun _ => false := by
        funext i; simp
      rw [this]
      simp [Fg, F]
    rw [inv_eq_of_mul_eq_one_left h]
  let K : Subgroup G :=
    { carrier := Set.range Fg
      one_mem' := ⟨fun _ : Fin n => false, by simp [Fg, F]⟩
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨fun i => Bool.xor (a i) (b i), (hFg_mul a b).symm⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a, (hFg_inv a).symm⟩ }
  have hFsingle : ∀ i, F (fun j : Fin n => decide (j = i)) = ec i := by
    intro i
    simp only [F, decide_eq_true_eq]
    rw [Finset.prod_ite_eq_of_mem' (Finset.univ) i (fun j => ec j) (Finset.mem_univ i)]
  have hgen : Set.range e ⊆ (K : Set G) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨fun j : Fin n => decide (j = i), ?_⟩
    show ((F (fun j : Fin n => decide (j = i)) : C) : G) = e i
    rw [hFsingle i]
  have hle : C ≤ K := (Subgroup.closure_le K).mpr hgen
  let g : (Fin n → Bool) → K := fun b => ⟨Fg b, ⟨b, rfl⟩⟩
  have hg : Function.Surjective g := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  haveI : Finite K := Finite.of_surjective g hg
  have hFinC : Finite C :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hcardC : Nat.card C ≤ Nat.card K := Subgroup.card_le_of_le hle
  have hcardK : Nat.card K ≤ Nat.card (Fin n → Bool) := Nat.card_le_card_of_surjective g hg
  have hcardDom : Nat.card (Fin n → Bool) = 2 ^ n := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_bool]
  exact ⟨hFinC, (hcardC.trans hcardK).trans_eq hcardDom⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

variable {X : Type} [Group X]

@[expose] def mono (g : Fin 5 → X) (v : Fin 5 → ZMod 2) : X :=
  g 0 ^ (v 0).val * g 1 ^ (v 1).val * g 2 ^ (v 2).val * g 3 ^ (v 3).val * g 4 ^ (v 4).val

structure IsE5 (g : Fin 5 → X) : Prop where
  sq : ∀ i, g i * g i = 1
  comm : ∀ i j, g i * g j = g j * g i

namespace IsE5

variable {g : Fin 5 → X} (h : IsE5 g)
include h

theorem commute (i j : Fin 5) : Commute (g i) (g j) := h.comm i j

theorem pow_val_add (i : Fin 5) (a b : ZMod 2) :
    g i ^ (a + b).val = g i ^ a.val * g i ^ b.val := by
  have h2 : g i ^ 2 = 1 := by rw [pow_two]; exact h.sq i
  rw [ZMod.val_add, ← pow_eq_pow_mod _ h2, pow_add]

theorem commute_pow (i j : Fin 5) (a b : ℕ) : Commute (g i ^ a) (g j ^ b) :=
  ((h.commute i j).pow_left a).pow_right b

theorem mono_zero : mono g 0 = 1 := by simp [mono]

theorem mono_add (v w : Fin 5 → ZMod 2) : mono g (v + w) = mono g v * mono g w := by
  unfold mono
  simp only [Pi.add_apply, h.pow_val_add]
  set A0 := g 0 ^ (v 0).val
  set A1 := g 1 ^ (v 1).val
  set A2 := g 2 ^ (v 2).val
  set A3 := g 3 ^ (v 3).val
  set A4 := g 4 ^ (v 4).val
  set B0 := g 0 ^ (w 0).val
  set B1 := g 1 ^ (w 1).val
  set B2 := g 2 ^ (w 2).val
  set B3 := g 3 ^ (w 3).val
  set B4 := g 4 ^ (w 4).val
  have c0 : Commute B0 A1 := h.commute_pow 0 1 _ _
  have c1 : Commute (B0 * B1) A2 :=
    (h.commute_pow 0 2 _ _).mul_left (h.commute_pow 1 2 _ _)
  have c2 : Commute (B0 * B1 * B2) A3 :=
    ((h.commute_pow 0 3 _ _).mul_left (h.commute_pow 1 3 _ _)).mul_left (h.commute_pow 2 3 _ _)
  have c3 : Commute (B0 * B1 * B2 * B3) A4 :=
    (((h.commute_pow 0 4 _ _).mul_left (h.commute_pow 1 4 _ _)).mul_left
      (h.commute_pow 2 4 _ _)).mul_left (h.commute_pow 3 4 _ _)
  calc A0 * B0 * (A1 * B1) * (A2 * B2) * (A3 * B3) * (A4 * B4)
      = (A0 * A1) * (B0 * B1) * (A2 * B2) * (A3 * B3) * (A4 * B4) := by
        rw [c0.mul_mul_mul_comm]
    _ = (A0 * A1 * A2) * (B0 * B1 * B2) * (A3 * B3) * (A4 * B4) := by
        rw [c1.mul_mul_mul_comm]
    _ = (A0 * A1 * A2 * A3) * (B0 * B1 * B2 * B3) * (A4 * B4) := by
        rw [c2.mul_mul_mul_comm]
    _ = (A0 * A1 * A2 * A3 * A4) * (B0 * B1 * B2 * B3 * B4) := by
        rw [c3.mul_mul_mul_comm]

theorem mono_single (i : Fin 5) : mono g (Pi.single i 1) = g i := by
  have h1 : (1 : ZMod 2).val = 1 := by decide
  fin_cases i <;> simp [mono, Pi.single_apply, h1]

theorem mono_self (v : Fin 5 → ZMod 2) : mono g v * mono g v = 1 := by
  rw [← h.mono_add]
  have : v + v = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    revert i
    intro i
    generalize v i = a
    revert a
    decide
  rw [this, h.mono_zero]

theorem mono_inv (v : Fin 5 → ZMod 2) : (mono g v)⁻¹ = mono g v :=
  inv_eq_of_mul_eq_one_right (h.mono_self v)

theorem mono_comm (v w : Fin 5 → ZMod 2) : mono g v * mono g w = mono g w * mono g v := by
  rw [← h.mono_add, ← h.mono_add, add_comm]

theorem conj_mono (ν : X) (c : Fin 5 → Fin 5 → ZMod 2)
    (hν : ∀ i, ν * g i * ν⁻¹ = mono g (c i)) (v : Fin 5 → ZMod 2) :
    ν * mono g v * ν⁻¹ = mono g (∑ i, v i • c i) := by
  have key : ∀ i, ν * g i ^ (v i).val * ν⁻¹ = mono g (v i • c i) := by
    intro i
    rw [← conj_pow, hν i]
    generalize v i = a
    have h0 : (0 : ZMod 2).val = 0 := rfl
    have h1 : (1 : ZMod 2).val = 1 := rfl
    obtain rfl | rfl : a = 0 ∨ a = 1 := by revert a; decide
    · rw [h0, pow_zero, zero_smul, h.mono_zero]
    · rw [h1, pow_one, one_smul]
  have hmul : ν * mono g v * ν⁻¹ =
      (ν * g 0 ^ (v 0).val * ν⁻¹) * (ν * g 1 ^ (v 1).val * ν⁻¹) *
        (ν * g 2 ^ (v 2).val * ν⁻¹) * (ν * g 3 ^ (v 3).val * ν⁻¹) *
        (ν * g 4 ^ (v 4).val * ν⁻¹) := by
    unfold mono
    group
  rw [hmul, key, key, key, key, key, Fin.sum_univ_five]
  simp only [h.mono_add]

theorem mem_closure_iff (y : X) :
    y ∈ Subgroup.closure (Set.range g) ↔ ∃ v, y = mono g v := by
  constructor
  · intro hy
    let S : Subgroup X :=
      { carrier := {y | ∃ v, y = mono g v}
        one_mem' := ⟨0, h.mono_zero.symm⟩
        mul_mem' := by
          rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
          exact ⟨v + w, (h.mono_add v w).symm⟩
        inv_mem' := by
          rintro _ ⟨v, rfl⟩
          exact ⟨v, h.mono_inv v⟩ }
    have hle : Subgroup.closure (Set.range g) ≤ S := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨Pi.single i 1, (h.mono_single i).symm⟩
    exact hle hy
  · rintro ⟨v, rfl⟩
    unfold mono
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 0)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 1)) _))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 2)) _))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 3)) _))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 4)) _)

theorem isPGroup_closure : IsPGroup 2 (Subgroup.closure (Set.range g)) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨y, hy⟩
  obtain ⟨v, rfl⟩ := (h.mem_closure_iff y).mp hy
  have h2 : orderOf (⟨mono g v, hy⟩ : Subgroup.closure (Set.range g)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [pow_two] using h.mono_self v
  have h2' : orderOf (⟨mono g v, hy⟩ : Subgroup.closure (Set.range g)) ∣ 2 ^ 1 := by
    rwa [pow_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2'
  exact ⟨k, hk⟩

theorem card_closure_of_injective (hinj : Function.Injective (mono g)) :
    Nat.card (Subgroup.closure (Set.range g)) = 32 := by
  have hset : (Subgroup.closure (Set.range g) : Set X) = Set.range (mono g) := by
    ext y
    simp only [SetLike.mem_coe, h.mem_closure_iff, Set.mem_range]
    constructor
    · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩
  have h1 : Nat.card (Subgroup.closure (Set.range g)) = Nat.card (Set.range (mono g)) := by
    rw [← hset]
    rfl
  rw [h1, Nat.card_range_of_injective hinj]
  simp [Nat.card_eq_fintype_card, ZMod.card]

end IsE5

end CFSG.ComponentClassification.SolMax.Sig36.E32

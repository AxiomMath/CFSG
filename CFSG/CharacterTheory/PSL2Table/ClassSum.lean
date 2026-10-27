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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.PSL2Table

open scoped BigOperators

variable {G : Type} [Group G]

@[expose] def conjSet (H : Subgroup G) : Set G := {y | y ≠ 1 ∧ ∃ g : G, g * y * g⁻¹ ∈ H}

theorem mem_conjSet_iff (H : Subgroup G) (y : G) :
    y ∈ conjSet H ↔ y ≠ 1 ∧ ∃ g : G, g * y * g⁻¹ ∈ H := Iff.rfl

theorem conj_mem_conjSet {H : Subgroup G} {y : G} (hy : y ∈ conjSet H) (k : G) :
    k * y * k⁻¹ ∈ conjSet H := by
  obtain ⟨hy1, g, hg⟩ := hy
  refine ⟨fun h => hy1 ?_, g * k⁻¹, ?_⟩
  · have := congrArg (fun z => k⁻¹ * z * k) h
    simpa [mul_assoc] using this
  · simpa [mul_assoc] using hg

theorem mem_conjSet_of_mem {H : Subgroup G} {x : G} (hx : x ∈ H) (hx1 : x ≠ 1) :
    x ∈ conjSet H := ⟨hx1, 1, by simpa using hx⟩

theorem orderOf_dvd_of_mem_conjSet [Finite G] {H : Subgroup G} {y : G} (hy : y ∈ conjSet H) :
    orderOf y ∣ Nat.card H := by
  obtain ⟨-, g, hg⟩ := hy
  have h := Subgroup.orderOf_dvd_natCard H hg
  have hconj : orderOf (g * y * g⁻¹) = orderOf y := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    simpa using this
  rwa [hconj] at h

theorem disjoint_conjSet [Finite G] {H K : Subgroup G} (hHK : Nat.Coprime (Nat.card H) (Nat.card K))
    {y : G} (hH : y ∈ conjSet H) (hK : y ∈ conjSet K) : False := by
  have h1 := orderOf_dvd_of_mem_conjSet hH
  have h2 := orderOf_dvd_of_mem_conjSet hK
  have h : orderOf y ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hHK] at this
  exact hH.1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h))

variable [Fintype G]

theorem card_conjugators_of_TI (H N : Subgroup G) [DecidablePred (· ∈ H)]
    (hTI : ∀ x ∈ H, x ≠ 1 → ∀ g : G, g * x * g⁻¹ ∈ H ↔ g ∈ N) {y : G} (hy : y ∈ conjSet H) :
    (Finset.univ.filter (fun g : G => g⁻¹ * y * g ∈ H)).card = Nat.card N := by
  obtain ⟨hy1, g₁, hg₁⟩ := hy
  have hx1 : g₁ * y * g₁⁻¹ ≠ 1 := by
    intro h
    apply hy1
    have := congrArg (fun z => g₁⁻¹ * z * g₁) h
    simpa [mul_assoc] using this
  have hiff : ∀ g : G, g⁻¹ * y * g ∈ H ↔ g₁ * g ∈ N := by
    intro g
    have h := hTI _ hg₁ hx1 (g₁ * g)⁻¹
    rw [inv_mem_iff] at h
    rw [← h]
    have : (g₁ * g)⁻¹ * (g₁ * y * g₁⁻¹) * (g₁ * g)⁻¹⁻¹ = g⁻¹ * y * g := by group
    rw [this]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun g => ⟨g₁ * g.1, (hiff g.1).mp g.2⟩
      invFun := fun n => ⟨g₁⁻¹ * n, (hiff _).mpr (by simp)⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun n => Subtype.ext (by simp) }

variable [DecidableEq G]

theorem sum_conj_of_TI (H N : Subgroup G) [DecidablePred (· ∈ H)]
    [DecidablePred (· ∈ conjSet H)]
    (hTI : ∀ x ∈ H, x ≠ 1 → ∀ g : G, g * x * g⁻¹ ∈ H ↔ g ∈ N) (f : G → ℂ) :
    ∑ g : G, ∑ x : G, (if x ∈ H ∧ x ≠ 1 then f (g * x * g⁻¹) else 0) =
      (Nat.card N : ℂ) * ∑ y : G, (if y ∈ conjSet H then f y else 0) := by
  have hreindex : ∀ g : G, ∑ x : G, (if x ∈ H ∧ x ≠ 1 then f (g * x * g⁻¹) else 0) =
      ∑ y : G, (if g⁻¹ * y * g ∈ H ∧ g⁻¹ * y * g ≠ 1 then f y else 0) := by
    intro g
    refine Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ (fun x => ?_)
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, this]
  simp_rw [hreindex]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hy : y ∈ conjSet H
  · simp only [hy, ↓reduceIte]
    have hne : ∀ g : G, g⁻¹ * y * g ≠ 1 := by
      intro g h
      apply hy.1
      have := congrArg (fun z => g * z * g⁻¹) h
      simpa [mul_assoc] using this
    simp only [hne, ne_eq, not_false_eq_true, and_true]
    rw [← Finset.sum_filter, Finset.sum_const, card_conjugators_of_TI H N hTI hy, nsmul_eq_mul]
  · simp only [hy, ↓reduceIte, mul_zero]
    refine Finset.sum_eq_zero (fun g _ => ?_)
    refine ite_eq_right_iff.mpr ?_
    rintro ⟨hmem, hne⟩
    exact (hy ⟨fun h => hne (by rw [h]; group), g⁻¹, by simpa using hmem⟩).elim

theorem sum_conjSet_of_TI (H N : Subgroup G) [DecidablePred (· ∈ H)]
    [DecidablePred (· ∈ conjSet H)]
    (hTI : ∀ x ∈ H, x ≠ 1 → ∀ g : G, g * x * g⁻¹ ∈ H ↔ g ∈ N) (f : G → ℂ)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x) :
    (Nat.card N : ℂ) * ∑ y : G, (if y ∈ conjSet H then f y else 0) =
      (Nat.card G : ℂ) * ∑ x : G, (if x ∈ H ∧ x ≠ 1 then f x else 0) := by
  rw [← sum_conj_of_TI H N hTI f]
  simp_rw [hf]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem card_conjSet_of_TI (H N : Subgroup G) [DecidablePred (· ∈ H)]
    [DecidablePred (· ∈ conjSet H)]
    (hTI : ∀ x ∈ H, x ≠ 1 → ∀ g : G, g * x * g⁻¹ ∈ H ↔ g ∈ N) :
    Nat.card N * (Finset.univ.filter (· ∈ conjSet H)).card =
      Nat.card G * ((Nat.card H) - 1) := by
  have h := sum_conjSet_of_TI H N hTI (fun _ => 1) (fun _ _ => rfl)
  simp only [Finset.sum_boole] at h
  have hH : (Finset.univ.filter (fun x : G => x ∈ H ∧ x ≠ 1)).card = Nat.card H - 1 := by
    have h1 : (Finset.univ.filter (fun x : G => x ∈ H ∧ x ≠ 1)) =
        (Finset.univ.filter (· ∈ H)).erase 1 := by
      ext x
      simp [and_comm]
    rw [h1, Finset.card_erase_of_mem (by simp [H.one_mem]), Nat.card_eq_fintype_card,
      ← Fintype.card_subtype]
  rw [hH] at h
  have hcast : ((Nat.card N * (Finset.univ.filter (· ∈ conjSet H)).card : ℕ) : ℂ) =
      ((Nat.card G * (Nat.card H - 1) : ℕ) : ℂ) := by
    push_cast
    rw [h]
  exact_mod_cast hcast

end CFSG.PSL2Table

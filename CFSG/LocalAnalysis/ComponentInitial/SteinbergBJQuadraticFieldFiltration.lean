module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

namespace CFSG.LocalAnalysis.ComponentInitial.QuadraticFieldFiltration

theorem add_pow_two_pow_of_commute {R : Type*} [Ring R] (h2 : ∀ z : R, z + z = 0) {x y : R}
    (hxy : Commute x y) (k : ℕ) : (x + y) ^ 2 ^ k = x ^ 2 ^ k + y ^ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : Commute (x ^ 2 ^ k) (y ^ 2 ^ k) := hxy.pow_pow _ _
    rw [pow_succ, pow_mul, ih, pow_mul, pow_mul, sq, sq, sq, add_mul, mul_add, mul_add, ← hc.eq]
    calc x ^ 2 ^ k * x ^ 2 ^ k + x ^ 2 ^ k * y ^ 2 ^ k +
          (x ^ 2 ^ k * y ^ 2 ^ k + y ^ 2 ^ k * y ^ 2 ^ k) =
        x ^ 2 ^ k * x ^ 2 ^ k + y ^ 2 ^ k * y ^ 2 ^ k +
          (x ^ 2 ^ k * y ^ 2 ^ k + x ^ 2 ^ k * y ^ 2 ^ k) := by abel
      _ = x ^ 2 ^ k * x ^ 2 ^ k + y ^ 2 ^ k * y ^ 2 ^ k := by rw [h2, add_zero]

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A]

abbrev toEnd (μ : Kˣ →* (AddMonoid.End A)ˣ) (l : Kˣ) : AddMonoid.End A := (μ l : AddMonoid.End A)

theorem toEnd_mul (μ : Kˣ →* (AddMonoid.End A)ˣ) (a b : Kˣ) :
    toEnd μ (a * b) = toEnd μ a * toEnd μ b := by
  rw [toEnd, map_mul, Units.val_mul]

theorem toEnd_pow (μ : Kˣ →* (AddMonoid.End A)ˣ) (a : Kˣ) (k : ℕ) :
    toEnd μ (a ^ k) = toEnd μ a ^ k := by
  rw [toEnd, map_pow, Units.val_pow_eq_pow_val]

theorem commute_toEnd (μ : Kˣ →* (AddMonoid.End A)ˣ) (a b : Kˣ) :
    Commute (toEnd μ a) (toEnd μ b) := by
  rw [Commute, SemiconjBy, ← toEnd_mul, ← toEnd_mul, mul_comm]

section Additive

variable [CharP K 2] {r : ℕ} (hA : ∀ x : A, x + x = 0) (μ : Kˣ →* (AddMonoid.End A)ˣ)
  (C : ℕ → AddSubgroup A)
  (hCinv : ∀ i ≤ r, ∀ (l : Kˣ) (x : A), x ∈ C i → (μ l : AddMonoid.End A) x ∈ C i)
  (φ : ∀ i : Fin r, (C (i + 1) ⧸ (C i).addSubgroupOf (C (i + 1))) ≃+ K)
  (hφ : ∀ (i : Fin r) (l : Kˣ) (x : C (i + 1)),
    φ i (⟨(μ l : AddMonoid.End A) x, hCinv _ i.2 l x x.2⟩ : C (i + 1)) =
      (l : K) * φ i (x : C (i + 1)))

include hφ in
theorem sum_apply_mem {a b c : Kˣ} (habc : (a : K) + b = c) (i : Fin r) {x : A}
    (hx : x ∈ C (i + 1)) : toEnd μ a x + toEnd μ b x + toEnd μ c x ∈ C i := by
  have hmem : toEnd μ a x + toEnd μ b x + toEnd μ c x ∈ C (i + 1) :=
    add_mem (add_mem (hCinv _ i.2 a x hx) (hCinv _ i.2 b x hx)) (hCinv _ i.2 c x hx)
  have hzero : ((⟨toEnd μ a x + toEnd μ b x + toEnd μ c x, hmem⟩ : C (i + 1)) :
      C (i + 1) ⧸ (C i).addSubgroupOf (C (i + 1))) = 0 := by
    apply (φ i).injective
    rw [map_zero]
    have e : (⟨toEnd μ a x + toEnd μ b x + toEnd μ c x, hmem⟩ : C (i + 1)) =
        ⟨toEnd μ a x, hCinv _ i.2 a x hx⟩ + ⟨toEnd μ b x, hCinv _ i.2 b x hx⟩ +
          ⟨toEnd μ c x, hCinv _ i.2 c x hx⟩ := rfl
    rw [e, QuotientAddGroup.mk_add, QuotientAddGroup.mk_add, map_add, map_add,
      hφ i a ⟨x, hx⟩, hφ i b ⟨x, hx⟩, hφ i c ⟨x, hx⟩, ← habc]
    linear_combination ((a : K) + b) * φ i (⟨x, hx⟩ : C (i + 1)) *
      (CharTwo.two_eq_zero : (2 : K) = 0)
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hzero
  exact hzero

omit [CharP K 2] in
include hA in
theorem end_add_self (z : AddMonoid.End A) : z + z = 0 := by
  ext x
  exact hA (z x)

include hA hφ in
theorem map_add_apply [Finite K] (hC0 : C 0 = ⊥) (hCr : C r = ⊤) {a b c : Kˣ}
    (habc : (a : K) + b = c) (x : A) : toEnd μ a x + toEnd μ b x = toEnd μ c x := by
  set D : AddMonoid.End A := toEnd μ a + toEnd μ b + toEnd μ c with hD
  have hDapply : ∀ y : A, D y = toEnd μ a y + toEnd μ b y + toEnd μ c y := fun y => rfl
  have hDk : ∀ k ≤ r, ∀ y : A, (D ^ k) y ∈ C (r - k) := by
    intro k
    induction k with
    | zero =>
      intro _ y
      rw [Nat.sub_zero, hCr]
      exact AddSubgroup.mem_top _
    | succ k ih =>
      intro hk y
      have h1 := ih (by omega) y
      have hidx : ((⟨r - k - 1, by omega⟩ : Fin r) : ℕ) + 1 = r - k := by
        simp only
        omega
      have h2 := sum_apply_mem μ C hCinv φ hφ habc ⟨r - k - 1, by omega⟩ (x := (D ^ k) y)
        (by rw [hidx]; exact h1)
      rw [pow_succ']
      change D ((D ^ k) y) ∈ _
      rw [hDapply]
      have hidx' : r - (k + 1) = ((⟨r - k - 1, by omega⟩ : Fin r) : ℕ) := by
        simp only
        omega
      rw [hidx']
      exact h2
  have hDr : D ^ r = 0 := by
    ext y
    have := hDk r le_rfl y
    rw [Nat.sub_self, hC0, AddSubgroup.mem_bot] at this
    exact this
  have := Fintype.ofFinite K
  have hunit : ∀ l : Kˣ, l ^ Nat.card K = l := fun l => Units.ext (by
    rw [Units.val_pow_eq_pow_val, Nat.card_eq_fintype_card, FiniteField.pow_card])
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card K = 2 ^ n := by
    obtain ⟨n, hp, hcard⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hcard]⟩
  have hDq : D ^ Nat.card K = D := by
    have h2 := end_add_self hA
    rw [hD, hn,
      add_pow_two_pow_of_commute h2 ((commute_toEnd μ a c).add_left (commute_toEnd μ b c)),
      add_pow_two_pow_of_commute h2 (commute_toEnd μ a b), ← toEnd_pow, ← toEnd_pow, ← toEnd_pow,
      ← hn, hunit, hunit, hunit]
  have hDqj : ∀ j : ℕ, D ^ (Nat.card K ^ j) = D := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_one]
    | succ j ih => rw [pow_succ, pow_mul, ih, hDq]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hlt : r ≤ Nat.card K ^ r := by
    calc r ≤ 2 ^ r := Nat.lt_two_pow_self.le
      _ ≤ Nat.card K ^ r := Nat.pow_le_pow_left hq r
  have hD0 : D = 0 := by
    rw [← hDqj r, ← Nat.sub_add_cancel hlt, pow_add, hDr, mul_zero]
  have hx := congrArg (fun f : AddMonoid.End A => f x) hD0
  simp only [hDapply, AddMonoid.End.zero_apply] at hx
  calc toEnd μ a x + toEnd μ b x = toEnd μ a x + toEnd μ b x + toEnd μ c x + toEnd μ c x := by
        rw [add_assoc _ (toEnd μ c x), hA, add_zero]
    _ = toEnd μ c x := by rw [hx, zero_add]

end Additive

theorem quadratic_field_scalar_filtration_fixed_commutators {m r : ℕ} {K : Type*} [Field K]
    (hK : Nat.card K = 2 ^ (2 * m)) {A : Type*} [AddCommGroup A] [Finite A]
    (hA : ∀ x : A, x + x = 0) (μ : Kˣ →* (AddMonoid.End A)ˣ) (C : ℕ → AddSubgroup A)
    (hC0 : C 0 = ⊥) (hCr : C r = ⊤) (hCmono : ∀ i < r, C i ≤ C (i + 1))
    (hCinv : ∀ i ≤ r, ∀ (l : Kˣ) (x : A), x ∈ C i → (μ l : AddMonoid.End A) x ∈ C i)
    (φ : ∀ i : Fin r, (C (i + 1) ⧸ (C i).addSubgroupOf (C (i + 1))) ≃+ K)
    (hφ : ∀ (i : Fin r) (l : Kˣ) (x : C (i + 1)),
      φ i (⟨(μ l : AddMonoid.End A) x, hCinv _ i.2 l x x.2⟩ : C (i + 1)) =
        (l : K) * φ i (x : C (i + 1)))
    (ν : A ≃+ A) (hν : ∀ x, ν (ν x) = x)
    (hνμ : ∀ (l : Kˣ) (x : A),
      ν ((μ l : AddMonoid.End A) (ν.symm x)) = (μ (l ^ 2 ^ m) : AddMonoid.End A) x) :
    {x : A | ν x = x} = Set.range (fun x => ν x - x) ∧
      Nat.card {x : A // ν x = x} = 2 ^ (m * r) ∧
      ∃ f : A →+ A, ∀ x, f x = ν x - x := by
  classical
  have hKf : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · have := Finite.one_lt_card (α := K)
      rw [hK, h, mul_zero, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact h
  have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, hK⟩
  have : CharP K 2 := hU.charP
  obtain ⟨ρ₀, hρ₀⟩ := (unitary_field_trace hU).1 1
  have hρ : ρ₀ + ρ₀ ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hρ₀
    exact this
  have hρ0 : ρ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ two_ne_zero), add_zero] at hρ
    exact zero_ne_one hρ
  set ρ : Kˣ := Units.mk0 ρ₀ hρ0 with hρdef
  have hsum : ((ρ ^ 2 ^ m : Kˣ) : K) + (ρ : K) = ((1 : Kˣ) : K) := by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, add_comm]
    exact hρ
  let Nν : A →+ A := ν.toAddMonoidHom + AddMonoidHom.id A
  have hN : ∀ x, Nν x = ν x + x := fun x => rfl
  have hνν : ∀ x, ν (ν x) = x := hν
  have hneg : ∀ x : A, -x = x := fun x => neg_eq_of_add_eq_zero_left (hA x)
  have hνμx : ∀ (l : Kˣ) (x : A), ν (toEnd μ l x) = toEnd μ (l ^ 2 ^ m) (ν x) := by
    intro l x
    have := hνμ l (ν x)
    rwa [AddEquiv.symm_apply_apply] at this
  have hker : ∀ x, x ∈ Nν.ker ↔ ν x = x := by
    intro x
    rw [AddMonoidHom.mem_ker, hN]
    constructor
    · intro h
      rw [eq_neg_of_add_eq_zero_left h, hneg]
    · intro h
      rw [h, hA]
  have hrange_le : Nν.range ≤ Nν.ker := by
    rintro _ ⟨y, rfl⟩
    rw [hker, hN, map_add, hνν, add_comm]
  have hker_le : Nν.ker ≤ Nν.range := by
    intro x hx
    rw [hker] at hx
    refine ⟨toEnd μ ρ x, ?_⟩
    rw [hN, hνμx, hx]
    exact (map_add_apply hA μ C hCinv φ hφ hC0 hCr hsum x).trans (by
      rw [toEnd, map_one, Units.val_one]
      rfl)
  have hkr : Nν.ker = Nν.range := le_antisymm hker_le hrange_le
  have hcardC : ∀ i ≤ r, Nat.card (C i) = Nat.card K ^ i := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hC0, AddSubgroup.card_bot, pow_zero]
    | succ i ih =>
      intro hi
      have hle := hCmono i (by omega)
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ((C i).addSubgroupOf (C (i + 1))),
        Nat.card_congr (φ ⟨i, by omega⟩).toEquiv,
        Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv, ih (by omega), pow_succ,
        mul_comm]
  have hcardA : Nat.card A = 2 ^ (m * r) * 2 ^ (m * r) := by
    have h := hcardC r le_rfl
    rw [hCr, AddSubgroup.card_top, hK, ← pow_mul] at h
    rw [h, ← pow_add]
    ring_nf
  have hfirst : Nat.card A = Nat.card Nν.ker * Nat.card Nν.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Nν.ker, mul_comm,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Nν).toEquiv]
  have hcardker : Nat.card Nν.ker = 2 ^ (m * r) := by
    rw [hcardA, ← hkr] at hfirst
    exact Nat.mul_self_inj.mp hfirst.symm
  refine ⟨?_, ?_, ⟨ν.toAddMonoidHom - AddMonoidHom.id A, fun x => rfl⟩⟩
  · ext x
    rw [Set.mem_ofPred_eq, ← hker, hkr, Set.mem_range, AddMonoidHom.mem_range]
    refine exists_congr fun y => ?_
    rw [hN, sub_eq_add_neg, hneg]
  · rw [← hcardker]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (hker x).symm)

end CFSG.LocalAnalysis.ComponentInitial.QuadraticFieldFiltration

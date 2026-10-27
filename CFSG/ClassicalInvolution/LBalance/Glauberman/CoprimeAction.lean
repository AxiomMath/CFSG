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
public import Mathlib.Order.CompletePartialOrder
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

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

section CoprimeAction

variable {A : Type*} [CommGroup A] (φ : MulAut A)

@[expose] def fixedSubgroup : Subgroup A where
  carrier := {a | φ a = a}
  mul_mem' {a b} ha hb := by
    change φ (a * b) = a * b
    rw [map_mul, show φ a = a from ha, show φ b = b from hb]
  one_mem' := map_one φ
  inv_mem' {a} ha := by
    change φ a⁻¹ = a⁻¹
    rw [map_inv, show φ a = a from ha]

theorem mem_fixedSubgroup {a : A} : a ∈ fixedSubgroup φ ↔ φ a = a := Iff.rfl

@[expose] def commutatorHom : A →* A where
  toFun a := a * (φ a)⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    rw [mul_comm (φ b)⁻¹ (φ a)⁻¹]
    exact mul_mul_mul_comm a b _ _

@[expose] def commutatorSubgroup : Subgroup A := (commutatorHom φ).range

theorem mem_commutatorSubgroup {x : A} : x ∈ commutatorSubgroup φ ↔ ∃ a, a * (φ a)⁻¹ = x :=
  MonoidHom.mem_range

theorem mul_inv_apply_mem_commutatorSubgroup (a : A) : a * (φ a)⁻¹ ∈ commutatorSubgroup φ :=
  (mem_commutatorSubgroup φ).2 ⟨a, rfl⟩

theorem apply_mem_commutatorSubgroup {x : A} (hx : x ∈ commutatorSubgroup φ) :
    φ x ∈ commutatorSubgroup φ := by
  obtain ⟨a, rfl⟩ := (mem_commutatorSubgroup φ).1 hx
  refine (mem_commutatorSubgroup φ).2 ⟨φ a, ?_⟩
  simp

@[expose] def normHom (n : ℕ) : A →* A where
  toFun a := ∏ i ∈ Finset.range n, (φ ^ i) a
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    exact Finset.prod_mul_distrib

theorem normHom_apply (n : ℕ) (a : A) : normHom φ n a = ∏ i ∈ Finset.range n, (φ ^ i) a := rfl

variable {φ}

theorem pow_apply_apply (i : ℕ) (a : A) : (φ ^ i) (φ a) = φ ((φ ^ i) a) := by
  rw [← MulAut.mul_apply, ← pow_succ, pow_succ']
  rfl

theorem normHom_apply_apply {n : ℕ} (hn : φ ^ n = 1) (a : A) :
    normHom φ n (φ a) = normHom φ n a := by
  simp only [normHom_apply]
  have h1 : ∀ i : ℕ, (φ ^ i) (φ a) = (φ ^ (i + 1)) a := fun i => by
    rw [pow_succ]
    rfl
  simp only [h1]
  have h2 := Finset.prod_range_succ (fun i => (φ ^ i) a) n
  have h3 := Finset.prod_range_succ' (fun i => (φ ^ i) a) n
  have h4 : (φ ^ n) a = (φ ^ 0) a := by rw [hn, pow_zero]
  rw [h2, h4] at h3
  exact (mul_right_cancel h3).symm

theorem apply_normHom {n : ℕ} (hn : φ ^ n = 1) (a : A) :
    φ (normHom φ n a) = normHom φ n a := by
  refine Eq.trans ?_ (normHom_apply_apply hn a)
  simp only [normHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pow_apply_apply]

theorem normHom_of_mem_fixedSubgroup {n : ℕ} {f : A} (hf : f ∈ fixedSubgroup φ) :
    normHom φ n f = f ^ n := by
  have h : ∀ i : ℕ, (φ ^ i) f = f := fun i => by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ', MulAut.mul_apply]
      exact (congrArg φ ih).trans hf
  simp [normHom_apply, h]

theorem normHom_eq_one_of_mem_commutatorSubgroup {n : ℕ} (hn : φ ^ n = 1) {x : A}
    (hx : x ∈ commutatorSubgroup φ) : normHom φ n x = 1 := by
  obtain ⟨a, rfl⟩ := (mem_commutatorSubgroup φ).1 hx
  rw [map_mul, map_inv, normHom_apply_apply hn, mul_inv_cancel]

theorem mul_inv_pow_apply_mem_commutatorSubgroup (i : ℕ) (a : A) :
    a * ((φ ^ i) a)⁻¹ ∈ commutatorSubgroup φ := by
  induction i generalizing a with
  | zero => simp
  | succ i ih =>
    have h := (commutatorSubgroup φ).mul_mem (mul_inv_apply_mem_commutatorSubgroup φ a) (ih (φ a))
    have e : a * ((φ ^ (i + 1)) a)⁻¹ = a * (φ a)⁻¹ * (φ a * ((φ ^ i) (φ a))⁻¹) := by
      rw [pow_succ]
      change a * ((φ ^ i) (φ a))⁻¹ = _
      rw [mul_assoc, ← mul_assoc (φ a)⁻¹, inv_mul_cancel, one_mul]
    rw [e]
    exact h

theorem pow_mul_inv_normHom_mem_commutatorSubgroup (n : ℕ) (a : A) :
    a ^ n * (normHom φ n a)⁻¹ ∈ commutatorSubgroup φ := by
  have e : a ^ n * (normHom φ n a)⁻¹ = ∏ i ∈ Finset.range n, (a * ((φ ^ i) a)⁻¹) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_inv_distrib]
    rfl
  rw [e]
  exact Subgroup.prod_mem _ fun i _ => mul_inv_pow_apply_mem_commutatorSubgroup i a

theorem fixedSubgroup_inf_commutatorSubgroup {n : ℕ} (hn : φ ^ n = 1)
    (hcop : Nat.Coprime n (Nat.card A)) :
    fixedSubgroup φ ⊓ commutatorSubgroup φ = ⊥ := by
  rw [eq_bot_iff]
  rintro f ⟨hf, hfR⟩
  have h1 : f ^ n = 1 := by
    rw [← normHom_of_mem_fixedSubgroup hf]
    exact normHom_eq_one_of_mem_commutatorSubgroup hn hfR
  have h2 : f ^ Nat.card A = 1 := pow_card_eq_one'
  have h3 : orderOf f = 1 :=
    Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1))
      (orderOf_dvd_of_pow_eq_one h2)
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h3)

theorem fixedSubgroup_sup_commutatorSubgroup [Finite A] {n : ℕ} (hn : φ ^ n = 1)
    (hcop : Nat.Coprime n (Nat.card A)) :
    fixedSubgroup φ ⊔ commutatorSubgroup φ = ⊤ := by
  rw [eq_top_iff]
  intro a _
  have hpos : Nat.card A ≠ 0 := Nat.card_pos.ne'
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop hpos
  have hpow : a = (a ^ n) ^ m := by
    rw [← pow_mul, ← pow_mod_natCard, hm, pow_mod_natCard, pow_one]
  have hnorm : normHom φ n a ∈ fixedSubgroup φ := apply_normHom hn a
  have hdecomp : a = (a ^ n * (normHom φ n a)⁻¹) ^ m * (normHom φ n a) ^ m := by
    rw [← mul_pow, inv_mul_cancel_right]
    exact hpow
  rw [hdecomp, mul_comm]
  exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ hnorm m)
    (Subgroup.pow_mem _ (pow_mul_inv_normHom_mem_commutatorSubgroup n a) m)

end CoprimeAction

end CFSG.ClassicalInvolution.GlaubermanAut

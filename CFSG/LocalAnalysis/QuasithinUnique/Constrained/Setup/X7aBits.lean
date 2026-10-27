module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Colex
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Setup.X7a

section Bits

variable {f : ℕ}

@[expose] def mBits (a : Fin f → Bool) : ℕ := ∑ i : Fin f, if a i then 2 ^ (i : ℕ) else 0

@[expose] def cntS (a b : Fin f → Bool) : ℕ := (Finset.univ.filter fun i => a i ≠ b i).card

@[expose] def cntH (a b : Fin f → Bool) : ℕ :=
  (Finset.univ.filter fun i => a i = true ∧ b i = true).card

@[expose] def zeros (f : ℕ) : Fin f → Bool := fun _ => false

@[expose] def ones (f : ℕ) : Fin f → Bool := fun _ => true

@[expose] def bitSupp (a : Fin f → Bool) : Finset ℕ :=
  (Finset.univ.filter fun i : Fin f => a i = true).image (fun i : Fin f => (i : ℕ))

theorem mBits_eq_sum_supp (a : Fin f → Bool) : mBits a = ∑ j ∈ bitSupp a, 2 ^ j := by
  rw [bitSupp, Finset.sum_image (fun x _ y _ h => Fin.ext h), Finset.sum_filter]
  unfold mBits
  refine Finset.sum_congr rfl fun i _ => ?_
  cases a i <;> simp

theorem mBits_lt (a : Fin f → Bool) : mBits a < 2 ^ f := by
  rw [mBits_eq_sum_supp]
  refine Nat.geomSum_lt le_rfl ?_
  intro j hj
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
  exact i.2

theorem mBits_injective : Function.Injective (mBits (f := f)) := by
  intro a a' h
  rw [mBits_eq_sum_supp, mBits_eq_sum_supp] at h
  have h2 := Finset.equivBitIndices.symm.injective (a₁ := bitSupp a) (a₂ := bitSupp a')
    (by simpa using h)
  funext i
  have h3 : (i : ℕ) ∈ bitSupp a ↔ (i : ℕ) ∈ bitSupp a' := by rw [h2]
  simp only [bitSupp, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h3
  have h4 : a i = true ↔ a' i = true := by
    constructor
    · intro hy
      obtain ⟨j, hj, hje⟩ := h3.mp ⟨i, hy, rfl⟩
      rwa [Fin.ext hje] at hj
    · intro hy
      obtain ⟨j, hj, hje⟩ := h3.mpr ⟨i, hy, rfl⟩
      rwa [Fin.ext hje] at hj
  cases ha : a i <;> cases ha' : a' i <;> simp_all

theorem mBits_zeros : mBits (zeros f) = 0 := by
  simp [mBits, zeros]

theorem mBits_eq_zero {a : Fin f → Bool} (h : mBits a = 0) : a = zeros f := by
  funext i
  have := (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
  cases ha : a i
  · rfl
  · rw [ha] at this
    simp at this

theorem mBits_ones : mBits (ones f) = 2 ^ f - 1 := by
  simp only [mBits, ones, ite_true]
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) f, Nat.geomSum_eq (le_refl 2)]
  simp

theorem eq_ones_of_mBits {a : Fin f → Bool} (h : mBits a = 2 ^ f - 1) : a = ones f := by
  funext i
  by_contra hne
  have ha : a i = false := by
    cases ha : a i
    · rfl
    · exact absurd ha (by simpa [ones] using hne)
  have hlt : mBits a < mBits (ones f) := by
    unfold mBits
    refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · cases a j <;> simp [ones]
    · simp [ones, ha]
  rw [mBits_ones, h] at hlt
  exact lt_irrefl _ hlt

theorem torus_weight_eq {F : Type*} [Field F] [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : ∀ z : Fˣ, z ^ a = z ^ b) :
    a = b ∨ (a = 0 ∧ b = 2 ^ n - 1) ∨ (b = 0 ∧ a = 2 ^ n - 1) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card, hF]
  have hmod : a ≡ b [MOD 2 ^ n - 1] := by
    rw [← hord]; exact pow_eq_pow_iff_modEq.mp (h g)
  unfold Nat.ModEq at hmod
  have key : ∀ x : ℕ, x < 2 ^ n → (x < 2 ^ n - 1 ∧ x % (2 ^ n - 1) = x) ∨
      (x = 2 ^ n - 1 ∧ x % (2 ^ n - 1) = 0) := by
    intro x hx
    by_cases hxN : x < 2 ^ n - 1
    · exact Or.inl ⟨hxN, Nat.mod_eq_of_lt hxN⟩
    · right
      have : x = 2 ^ n - 1 := by omega
      exact ⟨this, by rw [this, Nat.mod_self]⟩
  rcases key a ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rcases key b hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · left; rw [← ha2, ← hb2]; exact hmod
  · right; left; exact ⟨by rw [← ha2, hmod, hb2], hb1⟩
  · right; right; exact ⟨by rw [← hb2, ← hmod, ha2], ha1⟩
  · left; omega

end Bits

end CFSG.QuasithinUnique.Setup.X7a

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

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem pow_sub_one_apply_eq_zero (g : Module.End K V) (F : ℕ → Submodule K V)
    (hF0 : F 0 = ⊥) (htriv : ∀ i, ∀ v ∈ F (i + 1), (g - 1) v ∈ F i) :
    ∀ i, ∀ v ∈ F i, ((g - 1) ^ i) v = 0 := by
  intro i
  induction i with
  | zero =>
    intro v hv
    rw [hF0, Submodule.mem_bot] at hv
    simp [hv]
  | succ i ih =>
    intro v hv
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (htriv i v hv)

theorem pow_two_pow_eq_one_of_trivial_graded [CharP K 2] (g : Module.End K V)
    (F : ℕ → Submodule K V) (hF0 : F 0 = ⊥)
    (htriv : ∀ i, ∀ v ∈ F (i + 1), (g - 1) v ∈ F i)
    {N : ℕ} (hN : F N = ⊤) {k : ℕ} (hk : N ≤ 2 ^ k) : g ^ (2 ^ k) = 1 := by
  by_cases hV : Nontrivial V
  · have h1 : CharP (Module.End K V) 2 :=
      charP_of_injective_algebraMap (algebraMap K (Module.End K V)).injective 2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsub := sub_pow_char_pow_of_commute 2 k (Commute.one_right g)
    simp only [one_pow] at hsub
    have hzero : (g - 1) ^ (2 ^ k) = 0 := by
      ext v
      have h2 : ∀ w, ((g - 1) ^ N) w = 0 := fun w =>
        pow_sub_one_apply_eq_zero g F hF0 htriv N w (hN ▸ trivial)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
      rw [hd, pow_add, Module.End.mul_apply, h2]
      simp
    rw [hsub] at hzero
    exact sub_eq_zero.mp hzero
  · rw [not_nontrivial_iff_subsingleton] at hV
    exact Subsingleton.elim _ _

theorem eq_one_of_pow_three_pow_of_trivial_graded [CharP K 2] (g : LinearMap.GeneralLinearGroup K V)
    {j : ℕ} (hg : g ^ 3 ^ j = 1) (F : ℕ → Submodule K V) (hF0 : F 0 = ⊥)
    (htriv : ∀ i, ∀ v ∈ F (i + 1), ((g : Module.End K V) - 1) v ∈ F i)
    {N : ℕ} (hN : F N = ⊤) : g = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, N ≤ 2 ^ k := ⟨N, (Nat.lt_two_pow_self).le⟩
  have h2 : g ^ 2 ^ k = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact pow_two_pow_eq_one_of_trivial_graded (g : Module.End K V) F hF0 htriv hN hk
  have hcop : Nat.Coprime (3 ^ j) (2 ^ k) := (Nat.Coprime.pow j k (by norm_num))
  have h3 : orderOf g ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hg
  have h4 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have := Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h3 |>.coprime_dvd_right h4) (dvd_refl _)
  exact orderOf_eq_one_iff.mp (by simpa using this)

end CFSG.HardMathSupport.Curtis.UnitaryLevi

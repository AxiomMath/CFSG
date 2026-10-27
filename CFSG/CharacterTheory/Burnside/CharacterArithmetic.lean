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
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
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

namespace CFSG

namespace Burnside

open scoped BigOperators

private theorem Module.End.isIntegral_trace_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : 0 < n) (hpow : f ^ n = 1) :
    IsIntegral ℤ (LinearMap.trace ℂ V f) := by
  let s : Multiset ℂ := (LinearMap.charpoly f).roots
  have hroot_pow : ∀ z ∈ s, z ^ n = 1 := by
    intro z hz
    have heig : f.HasEigenvalue z :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f z).2
        (Polynomial.isRoot_of_mem_roots hz)
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hvpow := hv.pow_apply n
    rw [hpow, Module.End.one_apply] at hvpow
    have hzsmul : (z ^ n - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hvpow, sub_self]
    rcases smul_eq_zero.mp hzsmul with hz | hvzero
    · exact sub_eq_zero.mp hz
    · exact (hv.2 hvzero).elim
  have hroot_integral : ∀ z ∈ s, IsIntegral ℤ z := by
    intro z hz
    apply IsIntegral.of_pow hn
    rw [hroot_pow z hz]
    exact isIntegral_one
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits
    (f := f) (IsAlgClosed.splits (LinearMap.charpoly f))]
  exact IsIntegral.multiset_sum hroot_integral

theorem Representation.isIntegral_character_of_isOfFinOrder
    {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) (hg : IsOfFinOrder g) :
    IsIntegral ℤ (ρ.character g) := by
  obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
  apply Module.End.isIntegral_trace_of_pow_eq_one (ρ g) hn
  rw [← map_pow, hgn, map_one]

private theorem isIntegral_of_coprime_mul
    {z : ℂ} {c d : ℕ} (hcop : c.Coprime d)
    (hc : IsIntegral ℤ ((c : ℂ) * z))
    (hd : IsIntegral ℤ ((d : ℂ) * z)) :
    IsIntegral ℤ z := by
  have hbez :
      (1 : ℤ) = (c.gcdA d) * (c : ℤ) + (c.gcdB d) * (d : ℤ) := by
    rw [mul_comm (c.gcdA d), mul_comm (c.gcdB d), ← Nat.gcd_eq_gcd_ab]
    simp [hcop.gcd_eq_one]
  have hbezC :
      (1 : ℂ) = (c.gcdA d : ℂ) * (c : ℂ) + (c.gcdB d : ℂ) * (d : ℂ) := by
    exact_mod_cast hbez
  have hi : IsIntegral ℤ
      ((c.gcdA d : ℂ) * ((c : ℂ) * z) +
        (c.gcdB d : ℂ) * ((d : ℂ) * z)) := by
    simpa only [zsmul_eq_mul] using
      (hc.zsmul (c.gcdA d)).add (hd.zsmul (c.gcdB d))
  have heqz :
      (c.gcdA d : ℂ) * ((c : ℂ) * z) +
        (c.gcdB d : ℂ) * ((d : ℂ) * z) = z := by
    calc
      (c.gcdA d : ℂ) * ((c : ℂ) * z) +
          (c.gcdB d : ℂ) * ((d : ℂ) * z) =
          ((c.gcdA d : ℂ) * (c : ℂ) +
            (c.gcdB d : ℂ) * (d : ℂ)) * z := by ring
      _ = (1 : ℂ) * z := by rw [← hbezC]
      _ = z := one_mul z
  rw [heqz] at hi
  exact hi

theorem isIntegral_div_of_coprime_mul_eq_mul
    {χ ell : ℂ} {c d : ℕ} (hd0 : d ≠ 0) (hcop : c.Coprime d)
    (hχ : IsIntegral ℤ χ) (hell : IsIntegral ℤ ell)
    (heq : (c : ℂ) * χ = (d : ℂ) * ell) :
    IsIntegral ℤ (χ / (d : ℂ)) := by
  apply isIntegral_of_coprime_mul hcop
  · have hcdiv : (c : ℂ) * (χ / (d : ℂ)) = ell := by
      calc
        (c : ℂ) * (χ / (d : ℂ)) = ((c : ℂ) * χ) / (d : ℂ) := by ring
        _ = ((d : ℂ) * ell) / (d : ℂ) := by rw [heq]
        _ = ell := by field_simp
    rw [hcdiv]
    exact hell
  · have hddiv : (d : ℂ) * (χ / (d : ℂ)) = χ := by
      field_simp
    rw [hddiv]
    exact hχ

end Burnside

end CFSG

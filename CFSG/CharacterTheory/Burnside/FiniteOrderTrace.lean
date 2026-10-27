module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.StrictCombination
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG

namespace Burnside

open scoped BigOperators

private theorem Multiset.eq_of_mem_of_mem_of_norm_average_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
    (s : Multiset E) (hs : s ≠ 0) (hnorm : ∀ z ∈ s, ‖z‖ ≤ 1)
    (hav : ‖((s.card : ℝ)⁻¹) • s.sum‖ = 1)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) : x = y := by
  classical
  by_contra hxy
  have hcard_nat : s.card ≠ 0 := by
    intro h
    apply hs
    exact Multiset.card_eq_zero.mp h
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hsum_count : ∑ z ∈ s.toFinset, (Multiset.count z s : ℝ) / s.card = 1 := by
    rw [← Finset.sum_div]
    rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq, div_self hcard]
  have hpos_x : (Multiset.count x s : ℝ) / s.card ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast Multiset.count_ne_zero.mpr hx
    · exact hcard
  have hpos_y : (Multiset.count y s : ℝ) / s.card ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast Multiset.count_ne_zero.mpr hy
    · exact hcard
  have hlt := norm_sum_lt_of_strictConvexSpace
    (t := s.toFinset)
    (w := fun z => (Multiset.count z s : ℝ) / s.card)
    (r := 1) (z := fun z => z)
    (by intro z hz; positivity)
    hsum_count
    (show x ∈ s.toFinset from Multiset.mem_toFinset.mpr hx)
    (show y ∈ s.toFinset from Multiset.mem_toFinset.mpr hy)
    hxy hpos_x hpos_y
    (by
      intro z hz
      exact hnorm z (Multiset.mem_toFinset.mp hz))
  have hweighted :
      ∑ z ∈ s.toFinset, ((Multiset.count z s : ℝ) / s.card) • z =
        ((s.card : ℝ)⁻¹) • s.sum := by
    rw [Finset.sum_multiset_count s]
    simp_rw [div_eq_inv_mul, mul_smul, Nat.cast_smul_eq_nsmul]
    rw [Finset.smul_sum]
  rw [hweighted, hav] at hlt
  exact (lt_irrefl 1 hlt)

private theorem Module.End.eq_smul_one_of_pow_eq_one_of_norm_trace_div_finrank_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (f : Module.End ℂ V) {n : ℕ} (hn : 0 < n) (hpow : f ^ n = 1)
    (htrace : ‖LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)‖ = 1) :
    f = (LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)) • 1 := by
  classical
  let s : Multiset ℂ := (LinearMap.charpoly f).roots
  have hfinrank : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hcard : s.card = Module.finrank ℂ V := by
    dsimp [s]
    rw [IsAlgClosed.card_roots_eq_natDegree, LinearMap.charpoly_natDegree]
  have hs : s ≠ 0 := by
    intro hs0
    have : s.card = 0 := Multiset.card_eq_zero.mpr hs0
    rw [hcard] at this
    omega
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
  have hnorm : ∀ z ∈ s, ‖z‖ ≤ 1 := by
    intro z hz
    rw [Complex.norm_eq_one_of_pow_eq_one (hroot_pow z hz) hn.ne']
  have htrace_sum : LinearMap.trace ℂ V f = s.sum := by
    simpa [s] using
      (Module.End.trace_eq_sum_roots_charpoly_of_splits
        (f := f) (IsAlgClosed.splits (LinearMap.charpoly f)))
  have hav : ‖((s.card : ℝ)⁻¹) • s.sum‖ = 1 := by
    rw [hcard, ← htrace_sum]
    simpa [div_eq_mul_inv, mul_comm] using htrace
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero hs
  have hall : ∀ z ∈ s, z = ζ := by
    intro z hz
    exact Multiset.eq_of_mem_of_mem_of_norm_average_eq_one s hs hnorm hav hz hζ
  have hsrep : s = Multiset.replicate (Module.finrank ℂ V) ζ := by
    rw [Multiset.eq_replicate_of_mem hall, hcard]
  have hscalar_trace :
      LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ) = ζ := by
    rw [htrace_sum, hsrep]
    simp [hfinrank.ne']
  have hsemisimple : f.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    · apply Polynomial.Separable.squarefree
      exact Polynomial.X_pow_sub_one_separable_iff.mpr (by exact_mod_cast hn.ne')
    · simp [hpow]
  have hcharpoly :
      LinearMap.charpoly f =
        (Polynomial.X - Polynomial.C ζ) ^ Module.finrank ℂ V := by
    calc
      LinearMap.charpoly f =
          (Multiset.map (fun z => Polynomial.X - Polynomial.C z) s).prod := by
        simpa [s] using
          (IsAlgClosed.splits (LinearMap.charpoly f)).eq_prod_roots_of_monic
            (LinearMap.charpoly_monic f)
      _ = (Polynomial.X - Polynomial.C ζ) ^ Module.finrank ℂ V := by
        rw [hsrep]
        simp
  have hnilpotent : IsNilpotent (f - algebraMap ℂ (Module.End ℂ V) ζ) := by
    refine ⟨Module.finrank ℂ V, ?_⟩
    have hch := LinearMap.aeval_self_charpoly f
    rw [hcharpoly] at hch
    simpa using hch
  have hshift_semisimple :
      (f - algebraMap ℂ (Module.End ℂ V) ζ).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.mpr hsemisimple
  have hshift_zero : f - algebraMap ℂ (Module.End ℂ V) ζ = 0 :=
    Module.End.eq_zero_of_isNilpotent_isSemisimple hnilpotent hshift_semisimple
  rw [sub_eq_zero] at hshift_zero
  rw [hscalar_trace]
  simpa only [Algebra.smul_def, mul_one] using hshift_zero

theorem Module.End.eq_smul_one_of_pow_eq_one_of_trace_div_finrank_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (f : Module.End ℂ V) {n m : ℕ} (hn : 0 < n) (hpow : f ^ n = 1)
    (hm : 0 < m)
    (htrace_pow :
      (LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)) ^ m = 1) :
    f = (LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)) • 1 := by
  apply Module.End.eq_smul_one_of_pow_eq_one_of_norm_trace_div_finrank_eq_one
    f hn hpow
  exact Complex.norm_eq_one_of_pow_eq_one htrace_pow hm.ne'

theorem Module.End.eq_smul_one_of_pow_eq_one_of_numberField_trace
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (f : Module.End ℂ V) {n : ℕ} (hn : 0 < n) (hpow : f ^ n = 1)
    (K : Type*) [Field K] [NumberField K] (x : K) (ι : K →+* ℂ)
    (hx : x ≠ 0) (hxint : IsIntegral ℤ x)
    (hemb : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ 1)
    (htrace : LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ) = ι x) :
    f = (LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)) • 1 := by
  obtain ⟨m, hm, hxm⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hx hxint hemb
  apply Module.End.eq_smul_one_of_pow_eq_one_of_trace_div_finrank_pow_eq_one
    f hn hpow hm
  rw [htrace, ← map_pow, hxm, map_one]

end Burnside

end CFSG

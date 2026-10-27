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
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Rat.Star
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LyonsUnitaryFour

open Polynomial

theorem coeff_geom_mul_of_natDegree_lt {p s : ℕ} (Q : ℚ[X]) (hQ : ∀ k, s ≤ k → Q.coeff k = 0)
    {j : ℕ} (hs : 0 < s) (hj : j < p * s) :
    ((∑ i ∈ Finset.range p, (X ^ s : ℚ[X]) ^ i) * Q).coeff j = Q.coeff (j % s) := by
  rw [Finset.sum_mul, finsetSum_coeff]
  rw [Finset.sum_eq_single (j / s)]
  · rw [← pow_mul, coeff_X_pow_mul']
    rw [ite_eq_left (Nat.mul_div_le j s |>.trans' (by rw [mul_comm]))]
    congr 1
    rw [Nat.mod_eq_sub_mul_div]
  · intro i hi hne
    rw [← pow_mul, coeff_X_pow_mul']
    split_ifs with hle
    · apply hQ
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      ·
        have : s * i + s ≤ j := by
          have := (Nat.le_div_iff_mul_le hs).mp hlt
          nlinarith
        omega
      ·
        exfalso
        have : j < s * i := by
          have h := Nat.lt_mul_div_succ j hs
          nlinarith
        omega
    · rfl
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hj)

theorem periodic_of_sum_pow_eq_zero {p : ℕ} (hp : p.Prime) (b : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (p ^ (b + 1))) (c : ℕ → ℚ)
    (h : ∑ j ∈ Finset.range (p ^ (b + 1)), (c j : ℂ) * ζ ^ j = 0) {j : ℕ}
    (hj : j < p ^ (b + 1)) : c j = c (j % p ^ b) := by
  have hs : 0 < p ^ b := pow_pos hp.pos b
  have hN : p ^ (b + 1) = p * p ^ b := by rw [pow_succ, mul_comm]
  set F : ℚ[X] := ∑ i ∈ Finset.range (p ^ (b + 1)), C (c i) * X ^ i with hF
  have hcoeff : ∀ k, F.coeff k = if k < p ^ (b + 1) then c k else 0 := by
    intro k
    simp only [hF, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  have haeval : aeval ζ F = 0 := by
    simp only [hF, map_sum, map_mul, aeval_C, aeval_X_pow, eq_ratCast]
    exact h
  have hdvd : cyclotomic (p ^ (b + 1)) ℚ ∣ F := by
    rw [cyclotomic_eq_minpoly_rat hζ (pow_pos hp.pos _)]
    exact minpoly.dvd ℚ ζ haeval
  obtain ⟨Q, hQ⟩ := hdvd
  have hQdeg : ∀ k, p ^ b ≤ k → Q.coeff k = 0 := by
    by_cases hQ0 : Q = 0
    · intro k _
      simp [hQ0]
    intro k hk
    apply coeff_eq_zero_of_natDegree_lt
    have hFdeg : F.natDegree ≤ p ^ (b + 1) - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      have : ¬ k < p ^ (b + 1) := by omega
      simp [hcoeff, this]
    have hmul := natDegree_mul (cyclotomic_ne_zero (p ^ (b + 1)) ℚ) hQ0
    rw [← hQ, natDegree_cyclotomic, Nat.totient_prime_pow_succ hp] at hmul
    have hp2 := hp.two_le
    have : p ^ b * (p - 1) + p ^ b = p ^ (b + 1) := by
      rw [hN]
      have : p - 1 + 1 = p := by omega
      calc p ^ b * (p - 1) + p ^ b = p ^ b * (p - 1 + 1) := by ring
        _ = p * p ^ b := by rw [this, mul_comm]
    omega
  have hΦ : cyclotomic (p ^ (b + 1)) ℚ = ∑ i ∈ Finset.range p, (X ^ p ^ b : ℚ[X]) ^ i :=
    cyclotomic_prime_pow_eq_geom_sum hp
  rw [hΦ] at hQ
  have key : ∀ k < p ^ (b + 1), c k = Q.coeff (k % p ^ b) := by
    intro k hk
    have := hcoeff k
    simp only [hk, ite_true] at this
    rw [hQ, coeff_geom_mul_of_natDegree_lt Q hQdeg hs (by rw [← hN]; exact hk)] at this
    exact this.symm
  have hlt : j % p ^ b < p ^ (b + 1) :=
    lt_of_lt_of_le (Nat.mod_lt _ hs) (Nat.pow_le_pow_right hp.pos (Nat.le_succ b))
  rw [key j hj, key _ hlt, Nat.mod_mod]

theorem sum_range_mul_mod {M : Type*} [AddCommMonoid M] (g : ℕ → M) (q s : ℕ) :
    ∑ j ∈ Finset.range (q * s), g (j % s) = q • ∑ r ∈ Finset.range s, g r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]

theorem sum_toFinset_eq_sum_range_pow {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (s : Multiset ℂ) (hs : ∀ x ∈ s, x ^ N = 1) {M : Type*} [AddCommMonoid M] (f : ℂ → M)
    (hf : ∀ x, x ∉ s → f x = 0) :
    ∑ x ∈ s.toFinset, f x = ∑ j ∈ Finset.range N, f (ζ ^ j) := by
  classical
  have hsub : s.toFinset ⊆ (Finset.range N).image (ζ ^ ·) := by
    intro x hx
    rw [Multiset.mem_toFinset] at hx
    obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hs x hx)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  rw [Finset.sum_subset hsub (fun x _ hx => hf x (by rwa [Multiset.mem_toFinset] at hx)),
    Finset.sum_image]
  intro i hi j hj hij
  exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

theorem rational_sum_roots_of_unity {p : ℕ} (hp : p.Prime) (a : ℕ) (s : Multiset ℂ)
    (hs : ∀ x ∈ s, x ^ (p ^ a) = 1) {t : ℚ} (ht : s.sum = t) :
    (∃ z : ℤ, (z : ℚ) = t) ∧ (∃ K : ℕ, (Multiset.card s : ℚ) - t = p * K) ∧
      -((Multiset.card s : ℚ) / (p - 1)) ≤ t ∧
      ((Multiset.card s : ℚ) = t → ∀ x ∈ s, x = 1) := by
  classical
  have hp1 : (0 : ℚ) < p - 1 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  rcases a with _ | b
  ·
    have h1 : ∀ x ∈ s, x = 1 := fun x hx => by simpa using hs x hx
    have hsum : s.sum = Multiset.card s := by
      rw [Multiset.eq_replicate_of_mem h1]
      simp
    have htn : t = Multiset.card s := by
      have : ((t : ℂ)) = (Multiset.card s : ℂ) := by rw [← ht, hsum]
      exact_mod_cast this
    refine ⟨⟨Multiset.card s, by rw [htn]; simp⟩, ⟨0, by rw [htn]; simp⟩, ?_, fun _ => h1⟩
    rw [htn]
    have : 0 ≤ (Multiset.card s : ℚ) / (p - 1) := div_nonneg (Nat.cast_nonneg _) hp1.le
    linarith
  set N := p ^ (b + 1) with hNdef
  have hNpos : 0 < N := pow_pos hp.pos _
  have : NeZero N := ⟨hNpos.ne'⟩
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N hNpos.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / N)
  set m : ℕ → ℕ := fun j => s.count (ζ ^ j) with hm
  have hcard : (Multiset.card s : ℚ) = ∑ j ∈ Finset.range N, (m j : ℚ) := by
    rw [← Multiset.toFinset_sum_count_eq]
    push_cast
    exact sum_toFinset_eq_sum_range_pow hζ s hs (fun x => (s.count x : ℚ))
      (fun x hx => by simp [Multiset.count_eq_zero.mpr hx])
  have hsum : s.sum = ∑ j ∈ Finset.range N, (m j : ℂ) * ζ ^ j := by
    rw [Finset.sum_multiset_count]
    rw [sum_toFinset_eq_sum_range_pow hζ s hs (fun x => s.count x • x)
      (fun x hx => by simp [Multiset.count_eq_zero.mpr hx])]
    simp [hm, nsmul_eq_mul]
  set c : ℕ → ℚ := fun j => (m j : ℚ) - if j = 0 then t else 0 with hcdef
  have hc : ∑ j ∈ Finset.range N, (c j : ℂ) * ζ ^ j = 0 := by
    have h0 : (0 : ℕ) ∈ Finset.range N := Finset.mem_range.mpr hNpos
    simp only [hcdef, Rat.cast_sub, Rat.cast_natCast, sub_mul, Finset.sum_sub_distrib]
    rw [← hsum, ht]
    rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (fun h => absurd h0 h)]
    simp
  have hper : ∀ j < N, c j = c (j % p ^ b) := fun j hj =>
    periodic_of_sum_pow_eq_zero hp b hζ c hc hj
  have hsN : p ^ b < N := by
    rw [hNdef, pow_succ]
    have := hp.two_le
    nlinarith [pow_pos hp.pos b]
  have hspos : 0 < p ^ b := pow_pos hp.pos b
  have hNmul : N = p * p ^ b := by rw [hNdef, pow_succ, mul_comm]
  have hN2 : 2 * p ^ b ≤ N := by rw [hNmul]; exact Nat.mul_le_mul_right _ hp.two_le
  have hcr : ∀ r < p ^ b, c r = m (r + p ^ b) := by
    intro r hr
    have h1 := hper (r + p ^ b) (by omega)
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr] at h1
    rw [← h1]
    have hne : r + p ^ b ≠ 0 := by omega
    simp only [hcdef, hne, ite_false, sub_zero]
  have hc0 : c 0 = m 0 - t := by simp [hcdef]
  have hsumc : ∑ j ∈ Finset.range N, c j = (Multiset.card s : ℚ) - t := by
    simp only [hcdef]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', ← hcard]
    simp [hNpos]
  have hperiodic : ∑ j ∈ Finset.range N, c j = p * ∑ r ∈ Finset.range (p ^ b), c r := by
    rw [Finset.sum_congr rfl (fun j hj => hper j (Finset.mem_range.mp hj)), hNmul,
      sum_range_mul_mod c p (p ^ b), nsmul_eq_mul]
  set K := ∑ r ∈ Finset.range (p ^ b), m (r + p ^ b) with hK
  have hKc : ∑ r ∈ Finset.range (p ^ b), c r = K := by
    rw [hK]
    push_cast
    exact Finset.sum_congr rfl (fun r hr => hcr r (Finset.mem_range.mp hr))
  have hnt : (Multiset.card s : ℚ) - t = p * K := by rw [← hsumc, hperiodic, hKc]
  have ht0 : t = m 0 - m (p ^ b) := by
    have := hcr 0 hspos
    rw [zero_add] at this
    rw [hc0] at this
    linarith
  refine ⟨⟨(m 0 : ℤ) - m (p ^ b), by rw [ht0]; push_cast; ring⟩, ⟨K, hnt⟩, ?_, ?_⟩
  ·
    have hK0 : (m (0 + p ^ b) : ℚ) ≤ K := by
      rw [hK]
      push_cast
      exact Finset.single_le_sum (f := fun r => (m (r + p ^ b) : ℚ))
        (fun r _ => Nat.cast_nonneg _) (Finset.mem_range.mpr hspos)
    rw [zero_add] at hK0
    have hm0 : (0 : ℚ) ≤ m 0 := Nat.cast_nonneg _
    have hbound : ((p : ℚ) - 1) * m (p ^ b) ≤ Multiset.card s := by nlinarith
    rw [neg_le, le_div_iff₀ hp1]
    nlinarith
  ·
    intro hnt0
    have hK0 : K = 0 := by
      have : (p : ℚ) * K = 0 := by rw [← hnt, hnt0, sub_self]
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      exact_mod_cast (mul_eq_zero.mp this).resolve_left hp0
    have hmz : ∀ r < p ^ b, m (r + p ^ b) = 0 := by
      intro r hr
      have := Finset.sum_eq_zero_iff.mp (hK ▸ hK0) r (Finset.mem_range.mpr hr)
      exact this
    have hmj : ∀ j < N, j ≠ 0 → m j = 0 := by
      intro j hj hj0
      have h1 := hper j hj
      have h2 := hcr (j % p ^ b) (Nat.mod_lt _ hspos)
      rw [hmz _ (Nat.mod_lt _ hspos)] at h2
      have hcj : c j = m j := by simp only [hcdef, hj0, ite_false, sub_zero]
      have : (m j : ℚ) = 0 := by rw [← hcj, h1, h2]; simp
      exact_mod_cast this
    intro x hx
    obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hs x hx)
    by_contra hne
    have hj0 : j ≠ 0 := by rintro rfl; exact hne (pow_zero ζ)
    have := hmj j hj hj0
    rw [hm] at this
    exact (Multiset.count_eq_zero.mp this) hx

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem pow_eq_one_of_mem_roots_charpoly {f : Module.End ℂ V} {N : ℕ} (hf : f ^ N = 1) :
    ∀ x ∈ f.charpoly.roots, x ^ N = 1 := by
  intro x hx
  have hroot : f.charpoly.IsRoot x :=
    (Polynomial.mem_roots (LinearMap.charpoly_monic f).ne_zero).mp hx
  have hev : f.HasEigenvalue x := (Module.End.hasEigenvalue_iff_isRoot_charpoly f x).mpr hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h := hv.pow_apply N
  rw [hf, Module.End.one_apply] at h
  have h' : (1 - x ^ N) • v = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h' with h0 | h0
  · exact (sub_eq_zero.mp h0).symm
  · exact absurd h0 hv.2

theorem eq_one_of_pow_eq_one_of_roots {f : Module.End ℂ V} {N : ℕ} (hN : N ≠ 0)
    (hf : f ^ N = 1) (h1 : ∀ x ∈ f.charpoly.roots, x = 1) : f = 1 := by
  have hsep : (Polynomial.X ^ N - Polynomial.C (1 : ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hN) one_ne_zero
  have hsemi : f.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
    simp [hf]
  have hsemi' : (f - 1).IsSemisimple := by
    apply hsemi.of_mem_adjoin_singleton
    exact Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton ℂ f) (Subalgebra.one_mem _)
  have h0 : f - 1 = 0 := by
    rw [hsemi'.eq_zero_iff_forall_eigenvalue]
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hfv : f v = (μ + 1) • v := by
      have := hv.apply_eq_smul
      rw [LinearMap.sub_apply, Module.End.one_apply] at this
      rw [add_smul, one_smul, ← this, sub_add_cancel]
    have hev : f.HasEigenvalue (μ + 1) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hfv, hv.2⟩
    have hroot := (Module.End.hasEigenvalue_iff_isRoot_charpoly f _).mp hev
    have := h1 _ ((Polynomial.mem_roots (LinearMap.charpoly_monic f).ne_zero).mpr hroot)
    linear_combination this
  exact sub_eq_zero.mp h0

theorem trace_gap_of_pow_prime_pow_eq_one {p : ℕ} (hp : p.Prime) {a : ℕ}
    {f : Module.End ℂ V} (hf : f ^ (p ^ a) = 1) {t : ℚ} (ht : LinearMap.trace ℂ V f = t) :
    (∃ z : ℤ, (z : ℚ) = t) ∧ (∃ k : ℕ, (Module.finrank ℂ V : ℚ) - t = p * k) ∧
      -((Module.finrank ℂ V : ℚ) / (p - 1)) ≤ t ∧ t ≤ Module.finrank ℂ V ∧
      (f ≠ 1 → t < Module.finrank ℂ V) := by
  have hsplits : f.charpoly.Splits := IsAlgClosed.splits f.charpoly
  have hcard : Multiset.card f.charpoly.roots = Module.finrank ℂ V := by
    rw [← LinearMap.charpoly_natDegree f]
    exact (Polynomial.splits_iff_card_roots.mp hsplits)
  have hsum : f.charpoly.roots.sum = t := by
    rw [← Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits, ht]
  obtain ⟨hz, ⟨k, hk⟩, hlow, hone⟩ :=
    rational_sum_roots_of_unity hp a f.charpoly.roots (pow_eq_one_of_mem_roots_charpoly hf) hsum
  rw [hcard] at hk hlow hone
  have hup : t ≤ Module.finrank ℂ V := by
    have : (0 : ℚ) ≤ p * k := by positivity
    linarith
  refine ⟨hz, ⟨k, hk⟩, hlow, hup, fun hf1 => lt_of_le_of_ne hup fun heq => hf1 ?_⟩
  exact eq_one_of_pow_eq_one_of_roots (pow_ne_zero a hp.ne_zero) hf (hone heq.symm)

theorem trace_gap_exists_of_ne_one {p : ℕ} (hp : p.Prime) {a : ℕ} {f : Module.End ℂ V}
    (hf : f ^ (p ^ a) = 1) (hf1 : f ≠ 1) {t : ℚ} (ht : LinearMap.trace ℂ V f = t) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ Module.finrank ℂ V / (p - 1) ∧
      (Module.finrank ℂ V : ℚ) - t = p * k := by
  obtain ⟨-, ⟨k, hk⟩, hlow, -, hlt⟩ := trace_gap_of_pow_prime_pow_eq_one hp hf ht
  have hlt := hlt hf1
  have hp1 : (0 : ℚ) < p - 1 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  refine ⟨k, ?_, ?_, hk⟩
  · by_contra h0
    have : k = 0 := by omega
    rw [this] at hk
    push_cast at hk
    linarith
  · rw [Nat.le_div_iff_mul_le (by have := hp.two_le; omega)]
    have hle : -t * (p - 1) ≤ Module.finrank ℂ V := by
      rw [neg_le, le_div_iff₀ hp1] at hlow
      linarith
    have hkq : (k : ℚ) * (p - 1) ≤ Module.finrank ℂ V := by
      have hp0 : (0 : ℚ) < p := by linarith
      nlinarith
    have hcast : ((k * (p - 1) : ℕ) : ℚ) = (k : ℚ) * (p - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by have := hp.two_le; omega)]
      simp
    exact_mod_cast hcast ▸ hkq

theorem matrix_trace_gap_of_pow_prime_pow_eq_one {n p : ℕ} (hp : p.Prime) {a : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ^ (p ^ a) = 1) {t : ℚ} (ht : A.trace = t) :
    (∃ z : ℤ, (z : ℚ) = t) ∧ (∃ k : ℕ, (n : ℚ) - t = p * k) ∧
      -((n : ℚ) / (p - 1)) ≤ t ∧ t ≤ n ∧ (A ≠ 1 → t < n) := by
  have hf : (Matrix.toLin' A) ^ (p ^ a) = 1 := by
    rw [← Matrix.toLin'_pow, hA, Matrix.toLin'_one]; rfl
  have htr : LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLin' A) = t := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin', ht]
  have h := trace_gap_of_pow_prime_pow_eq_one hp hf htr
  rw [Module.finrank_fin_fun] at h
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun hA1 => h.2.2.2.2 fun h1 => hA1 ?_⟩
  have : Matrix.toLin' A = Matrix.toLin' 1 := by rw [h1, Matrix.toLin'_one]; rfl
  exact Matrix.toLin'.injective this

end CFSG.LyonsUnitaryFour

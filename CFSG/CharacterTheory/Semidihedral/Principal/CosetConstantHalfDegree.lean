module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
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

namespace CFSG.Semidihedral.Principal

namespace EigenCalculus

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
theorem eigenvalue_pow_eq_one {f : Module.End ℂ W} {n : ℕ} (hf : f ^ n = 1) {μ : ℂ}
    (hμ : f.HasEigenvalue μ) : μ ^ n = 1 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have h := hv.pow_apply n
  rw [hf, Module.End.one_apply] at h
  have h0 : (μ ^ n - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hv.2)

theorem isInternal_eigenspaces_of_family {f : Module.End ℂ W} {n : ℕ} (hn : n ≠ 0)
    (hf : f ^ n = 1) {ι : Type*} [DecidableEq ι] (ev : ι → ℂ) (hinj : Function.Injective ev)
    (hsurj : ∀ μ : ℂ, μ ^ n = 1 → ∃ j, ev j = μ) :
    DirectSum.IsInternal (fun j => f.eigenspace (ev j)) := by
  have hsemi : f.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := (Polynomial.X : Polynomial ℂ) ^ n - 1)
    · exact (Polynomial.X_pow_sub_one_separable_iff.2 (by exact_mod_cast hn)).squarefree
    · simp [hf]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact f.eigenspaces_iSupIndep.comp hinj
  · rw [eq_top_iff, ← hsemi.iSup_eigenspace_eq_top]
    refine iSup_le fun μ => ?_
    by_cases hμ : f.eigenspace μ = ⊥
    · rw [hμ]
      exact bot_le
    · obtain ⟨j, rfl⟩ :=
        hsurj μ (eigenvalue_pow_eq_one hf (Module.End.hasEigenvalue_iff.mpr hμ))
      exact le_iSup (fun j => f.eigenspace (ev j)) j

theorem isInternal_eigenspaces {f : Module.End ℂ W} {n : ℕ} (hn : n ≠ 0) (hf : f ^ n = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    DirectSum.IsInternal (fun j : Fin n => f.eigenspace (ζ ^ (j : ℕ))) := by
  have : NeZero n := ⟨hn⟩
  refine isInternal_eigenspaces_of_family hn hf (fun j : Fin n => ζ ^ (j : ℕ))
    (fun i j h => Fin.ext (hζ.pow_inj i.2 j.2 h)) fun μ hμ => ?_
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  exact ⟨⟨i, hi⟩, rfl⟩

theorem isInternal_eigenspaces_involution {f : Module.End ℂ W} (hf : f ^ 2 = 1) :
    DirectSum.IsInternal (fun j : Fin 2 => f.eigenspace (![1, -1] j)) := by
  refine isInternal_eigenspaces_of_family two_ne_zero hf _ ?_ fun μ hμ => ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (norm_num at h)
  · have h : (μ - 1) * (μ + 1) = 0 := by linear_combination hμ
    rcases mul_eq_zero.mp h with h | h
    · exact ⟨0, by simp; linear_combination -h⟩
    · exact ⟨1, by simp; linear_combination -h⟩

omit [FiniteDimensional ℂ W] in
theorem pow_apply_of_mem_eigenspace {f : Module.End ℂ W} {μ : ℂ} {v : W}
    (hv : v ∈ f.eigenspace μ) (i : ℕ) : (f ^ i) v = μ ^ i • v := by
  rw [Module.End.mem_eigenspace_iff] at hv
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]

omit [FiniteDimensional ℂ W] in
theorem mapsTo_eigenspace {f g : Module.End ℂ W} (hfg : Commute f g) (μ : ℂ) :
    ∀ v ∈ f.eigenspace μ, g v ∈ f.eigenspace μ := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  rw [← Module.End.mul_apply, hfg.eq, Module.End.mul_apply, hv, map_smul]

theorem trace_mul_pow_eq_sum_of_isInternal {f g : Module.End ℂ W} (hfg : Commute f g)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ev : ι → ℂ)
    (hN : DirectSum.IsInternal (fun j => f.eigenspace (ev j))) (i : ℕ) :
    LinearMap.trace ℂ W (g * f ^ i) = ∑ j, (ev j) ^ i *
      LinearMap.trace ℂ (f.eigenspace (ev j)) (g.restrict (mapsTo_eigenspace hfg (ev j))) := by
  have hcomm : Commute f (g * f ^ i) := hfg.mul_right (Commute.self_pow f i)
  rw [LinearMap.trace_eq_sum_trace_restrict hN (fun j => mapsTo_eigenspace hcomm (ev j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hres : (g * f ^ i).restrict (mapsTo_eigenspace hcomm (ev j)) =
      (ev j) ^ i • g.restrict (mapsTo_eigenspace hfg (ev j)) := by
    ext v
    have hpow := pow_apply_of_mem_eigenspace v.property i
    simp [LinearMap.restrict_apply, Module.End.mul_apply, hpow]
  rw [hres, map_smul, smul_eq_mul]

theorem trace_mul_pow_eq_sum {f g : Module.End ℂ W} (hfg : Commute f g) {n : ℕ} (hn : n ≠ 0)
    (hf : f ^ n = 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (i : ℕ) :
    LinearMap.trace ℂ W (g * f ^ i) = ∑ j : Fin n, (ζ ^ (j : ℕ)) ^ i *
      LinearMap.trace ℂ (f.eigenspace (ζ ^ (j : ℕ)))
        (g.restrict (mapsTo_eigenspace hfg (ζ ^ (j : ℕ)))) :=
  trace_mul_pow_eq_sum_of_isInternal hfg _ (isInternal_eigenspaces hn hf hζ) i

theorem sum_pow_root {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (j k : Fin n) :
    ∑ i ∈ Finset.range n, (ζ ^ (j : ℕ) * (ζ ^ (k : ℕ))⁻¹) ^ i =
      if j = k then (n : ℂ) else 0 := by
  by_cases hjk : j = k
  · subst hjk
    have hne : ζ ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (Fin.pos j).ne')
    simp [mul_inv_cancel₀ hne]
  · rw [ite_eq_right hjk]
    have hne : ζ ^ (j : ℕ) * (ζ ^ (k : ℕ))⁻¹ ≠ 1 := by
      intro h
      have hne0 : ζ ^ (k : ℕ) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (Fin.pos k).ne')
      exact hjk (Fin.ext (hζ.pow_inj j.2 k.2 (by
        rw [← mul_inv_eq_one₀ hne0]
        exact h)))
    rw [geom_sum_eq hne, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) n,
      mul_comm (k : ℕ) n, pow_mul, pow_mul, hζ.pow_eq_one, one_pow, one_pow, inv_one, mul_one,
      sub_self, zero_div]

theorem trace_restrict_eq_fourier {f g : Module.End ℂ W} (hfg : Commute f g) {n : ℕ}
    (hn : n ≠ 0) (hf : f ^ n = 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (k : Fin n) :
    LinearMap.trace ℂ (f.eigenspace (ζ ^ (k : ℕ)))
        (g.restrict (mapsTo_eigenspace hfg (ζ ^ (k : ℕ)))) =
      (n : ℂ)⁻¹ * ∑ i ∈ Finset.range n, ((ζ ^ (k : ℕ))⁻¹) ^ i *
        LinearMap.trace ℂ W (g * f ^ i) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  set T : Fin n → ℂ := fun j => LinearMap.trace ℂ (f.eigenspace (ζ ^ (j : ℕ)))
    (g.restrict (mapsTo_eigenspace hfg (ζ ^ (j : ℕ)))) with hT
  have hsum : ∑ i ∈ Finset.range n, ((ζ ^ (k : ℕ))⁻¹) ^ i * LinearMap.trace ℂ W (g * f ^ i) =
      (n : ℂ) * T k := by
    calc ∑ i ∈ Finset.range n, ((ζ ^ (k : ℕ))⁻¹) ^ i * LinearMap.trace ℂ W (g * f ^ i) =
        ∑ i ∈ Finset.range n, ∑ j : Fin n, ((ζ ^ (k : ℕ))⁻¹) ^ i * ((ζ ^ (j : ℕ)) ^ i * T j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [trace_mul_pow_eq_sum hfg hn hf hζ i, Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ i ∈ Finset.range n, (ζ ^ (j : ℕ) * (ζ ^ (k : ℕ))⁻¹) ^ i * T j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [mul_pow]
          ring
      _ = ∑ j : Fin n, (if j = k then (n : ℂ) else 0) * T j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul, sum_pow_root hζ j k]
      _ = (n : ℂ) * T k := by
          simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]

theorem finrank_eq_sum_of_isInternal {f : Module.End ℂ W} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ev : ι → ℂ) (hN : DirectSum.IsInternal (fun j => f.eigenspace (ev j))) :
    Module.finrank ℂ W = ∑ j, Module.finrank ℂ (f.eigenspace (ev j)) := by
  have h := trace_mul_pow_eq_sum_of_isInternal (Commute.one_right f) ev hN 0
  simp only [pow_zero, mul_one, LinearMap.trace_one, one_mul] at h
  have h' : ∀ j, LinearMap.trace ℂ (f.eigenspace (ev j))
      ((1 : Module.End ℂ W).restrict (mapsTo_eigenspace (Commute.one_right f) (ev j))) =
      Module.finrank ℂ (f.eigenspace (ev j)) := by
    intro j
    rw [show (1 : Module.End ℂ W).restrict (mapsTo_eigenspace (Commute.one_right f) (ev j)) = 1
      from by ext; rfl, LinearMap.trace_one]
  simp_rw [h'] at h
  exact_mod_cast h

theorem finrank_eq_sum {f : Module.End ℂ W} {n : ℕ} (hn : n ≠ 0) (hf : f ^ n = 1) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) :
    Module.finrank ℂ W = ∑ j : Fin n, Module.finrank ℂ (f.eigenspace (ζ ^ (j : ℕ))) :=
  finrank_eq_sum_of_isInternal _ (isInternal_eigenspaces hn hf hζ)

theorem norm_trace_le_finrank {s : Module.End ℂ W} {n : ℕ} (hn : n ≠ 0) (hs : s ^ n = 1) :
    ‖LinearMap.trace ℂ W s‖ ≤ Module.finrank ℂ W := by
  have hζ := Complex.isPrimitiveRoot_exp n hn
  have h := trace_mul_pow_eq_sum (Commute.one_right s) hn hs hζ 1
  simp only [pow_one, one_mul] at h
  rw [finrank_eq_sum hn hs hζ, Nat.cast_sum]
  have h1 : ∀ j : Fin n, LinearMap.trace ℂ (s.eigenspace (Complex.exp (2 * Real.pi *
      Complex.I / n) ^ (j : ℕ))) ((1 : Module.End ℂ W).restrict (mapsTo_eigenspace
        (Commute.one_right s) _)) = Module.finrank ℂ (s.eigenspace (Complex.exp (2 * Real.pi *
          Complex.I / n) ^ (j : ℕ))) := by
    intro j
    rw [show (1 : Module.End ℂ W).restrict (mapsTo_eigenspace (Commute.one_right s) _) = 1
      from by ext; rfl, LinearMap.trace_one]
  simp_rw [h1] at h
  rw [h]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [norm_mul, Complex.norm_natCast, norm_pow, hζ.norm'_eq_one hn, one_pow, one_mul]

end EigenCalculus

open EigenCalculus

theorem central_involution_coset_constant_half_degree {C V : Type*} [Group C] [Finite C]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ C V)
    {t : C} (htc : t ∈ Subgroup.center C) (ht : orderOf t = 2)
    (N : Subgroup C) [N.Normal] (_hNodd : Odd (Nat.card N))
    (hfaith : ∀ u ∈ N, ρ u = 1 → u = 1)
    (hrat : ∀ u ∈ N, ∃ q : ℚ, ρ.character u = q)
    (hconst : ∀ u ∈ N, ρ.character (t * u) = ρ.character t) :
    ∃ (k : ℤ) (r : ℕ), ρ.character t = k ∧ Module.finrank ℂ V = 2 * r + k.natAbs ∧
      ∃ (ε : ℂ) (hE : ∀ c : C, Module.End.eigenspace (ρ t) ε ≤
          (Module.End.eigenspace (ρ t) ε).comap (ρ c)),
        (ε = 1 ∨ ε = -1) ∧ Module.finrank ℂ (Module.End.eigenspace (ρ t) ε) = r ∧
        (∀ u ∈ N, ρ.character u =
          2 * (ρ.subrepresentation _ hE).character u + k.natAbs) ∧
        (∀ u ∈ N, ∃ q : ℚ, (ρ.subrepresentation _ hE).character u = q) ∧
        (∀ c : C, ∀ u ∈ N, (ρ.subrepresentation _ hE).character (c * u * c⁻¹) =
          (ρ.subrepresentation _ hE).character u) ∧
        (∀ u ∈ N, ρ.subrepresentation _ hE u = 1 → u = 1) ∧
        (N ≠ ⊥ → 0 < r) := by
  have hf2 : ρ t ^ 2 = 1 := by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  have hN := isInternal_eigenspaces_involution hf2
  have hcomm : ∀ c : C, Commute (ρ t) (ρ c) := fun c => by
    change ρ t * ρ c = ρ c * ρ t
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp htc c)]
  let ev : Fin 2 → ℂ := ![1, -1]
  let E : Fin 2 → Submodule ℂ V := fun j => Module.End.eigenspace (ρ t) (ev j)
  let T : C → Fin 2 → ℂ := fun c j => LinearMap.trace ℂ (E j)
    ((ρ c).restrict (mapsTo_eigenspace (hcomm c) (ev j)))
  have hsplit : ∀ c : C, ρ.character c = T c 0 + T c 1 ∧
      ρ.character (c * t) = T c 0 - T c 1 := by
    intro c
    have h0 := trace_mul_pow_eq_sum_of_isInternal (hcomm c) ev hN 0
    have h1 := trace_mul_pow_eq_sum_of_isInternal (hcomm c) ev hN 1
    rw [Fin.sum_univ_two] at h0 h1
    simp only [pow_zero, pow_one, mul_one, one_mul] at h0 h1
    refine ⟨h0, ?_⟩
    change LinearMap.trace ℂ V (ρ (c * t)) = _
    rw [map_mul, h1]
    change (1 : ℂ) * T c 0 + (-1) * T c 1 = _
    ring
  have hdim : ∀ j : Fin 2, T 1 j = Module.finrank ℂ (E j) := by
    intro j
    change LinearMap.trace ℂ _ ((ρ 1).restrict _) = _
    rw [show (ρ 1).restrict (mapsTo_eigenspace (hcomm 1) (ev j)) = 1 from by
      ext v; simp [LinearMap.restrict_apply], LinearMap.trace_one]
  set d₀ := Module.finrank ℂ (E 0) with hd₀
  set d₁ := Module.finrank ℂ (E 1) with hd₁
  have hcenter : ∀ u : C, u * t = t * u := fun u => Subgroup.mem_center_iff.mp htc u
  have hdiff : ∀ u ∈ N, T u 0 - T u 1 = ρ.character t := by
    intro u hu
    rw [← (hsplit u).2, hcenter u, hconst u hu]
  have hk : ρ.character t = ((d₀ : ℤ) - d₁ : ℤ) := by
    rw [← hdiff 1 N.one_mem, hdim 0, hdim 1]
    push_cast
    rfl
  have hfin : Module.finrank ℂ V = d₀ + d₁ := by
    have h := finrank_eq_sum_of_isInternal ev hN
    rw [Fin.sum_univ_two] at h
    exact h
  have hone : ∀ u ∈ N, ρ.character u = Module.finrank ℂ V → u = 1 := by
    intro u hu htr
    apply hfaith u hu
    refine CFSG.Section1.finite_order_eq_one_of_trace_eq_finrank (ρ u)
      (orderOf_pos u).ne' ?_ htr
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hinv : ∀ j : Fin 2, ∀ c : C, E j ≤ (E j).comap (ρ c) :=
    fun j c v hv => mapsTo_eigenspace (hcomm c) (ev j) v hv
  have hchar : ∀ j : Fin 2, ∀ c : C,
      (ρ.subrepresentation _ (hinv j)).character c = T c j := fun j c => rfl
  have hrank0 : ∀ j : Fin 2, Module.finrank ℂ (E j) = 0 →
      ∀ u : C, ρ.subrepresentation _ (hinv j) u = 1 := by
    intro j h u
    have : Subsingleton (E j) := Module.finrank_zero_iff.mp h
    exact Subsingleton.elim _ _
  have key : ∀ (j : Fin 2) (m : ℕ), Module.finrank ℂ (E j) = m →
      Module.finrank ℂ V = 2 * m + ((d₀ : ℤ) - d₁).natAbs →
      (∀ u ∈ N, ρ.character u = 2 * T u j + (((d₀ : ℤ) - d₁).natAbs : ℂ)) →
      ∃ (ε : ℂ) (hE : ∀ c : C, Module.End.eigenspace (ρ t) ε ≤
          (Module.End.eigenspace (ρ t) ε).comap (ρ c)),
        (ε = 1 ∨ ε = -1) ∧ Module.finrank ℂ (Module.End.eigenspace (ρ t) ε) = m ∧
        (∀ u ∈ N, ρ.character u =
          2 * (ρ.subrepresentation _ hE).character u + ((d₀ : ℤ) - d₁).natAbs) ∧
        (∀ u ∈ N, ∃ q : ℚ, (ρ.subrepresentation _ hE).character u = q) ∧
        (∀ c : C, ∀ u ∈ N, (ρ.subrepresentation _ hE).character (c * u * c⁻¹) =
          (ρ.subrepresentation _ hE).character u) ∧
        (∀ u ∈ N, ρ.subrepresentation _ hE u = 1 → u = 1) ∧
        (N ≠ ⊥ → 0 < m) := by
    intro j m hm hV hθ
    refine ⟨ev j, hinv j, ?_, hm, fun u hu => by rw [hchar, hθ u hu],
      fun u hu => ?_, fun c u _ => Representation.char_conj _ u c, fun u hu h1 => ?_, ?_⟩
    · fin_cases j
      · exact Or.inl rfl
      · exact Or.inr rfl
    · obtain ⟨q, hq⟩ := hrat u hu
      refine ⟨(q - ((d₀ : ℤ) - d₁).natAbs) / 2, ?_⟩
      rw [hchar]
      have := hθ u hu
      push_cast
      rw [← hq, this]
      ring
    · apply hone u hu
      have htr : T u j = m := by
        rw [← hchar, Representation.character, h1, LinearMap.trace_one, hm]
      rw [hθ u hu, htr, hV]
      push_cast
      ring
    · intro hNb
      by_contra h0
      have hm0 : m = 0 := by omega
      apply hNb
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_bot]
      refine hone u hu ?_
      have htr : T u j = 0 := by
        rw [← hchar, Representation.character, hrank0 j (by rw [hm, hm0]) u,
          LinearMap.trace_one, hm, hm0, Nat.cast_zero]
      rw [hθ u hu, htr, hV, hm0]
      push_cast
      ring
  refine ⟨(d₀ : ℤ) - d₁, if d₁ ≤ d₀ then d₁ else d₀, hk, ?_, ?_⟩
  · split_ifs with h
    · rw [hfin]
      omega
    · rw [hfin]
      omega
  · split_ifs with h
    · refine key 1 d₁ rfl (by rw [hfin]; omega) fun u hu => ?_
      have h1 := (hsplit u).1
      have h2 := hdiff u hu
      rw [hk] at h2
      have habs : (((d₀ : ℤ) - d₁).natAbs : ℂ) = (d₀ : ℂ) - d₁ := by
        have h' : ((d₀ : ℤ) - d₁).natAbs = d₀ - d₁ := by omega
        rw [h', Nat.cast_sub h]
      rw [habs, h1]
      push_cast at h2
      linear_combination h2
    · refine key 0 d₀ rfl (by rw [hfin]; omega) fun u hu => ?_
      have h1 := (hsplit u).1
      have h2 := hdiff u hu
      rw [hk] at h2
      have habs : (((d₀ : ℤ) - d₁).natAbs : ℂ) = (d₁ : ℂ) - d₀ := by
        have h' : ((d₀ : ℤ) - d₁).natAbs = d₁ - d₀ := by omega
        rw [h', Nat.cast_sub (by omega)]
      rw [habs, h1]
      push_cast at h2
      linear_combination -h2

end CFSG.Semidihedral.Principal

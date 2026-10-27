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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Module Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section CharP

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem X_sub_one_pow_char_pow (k : ℕ) : ((X : K[X]) - 1) ^ (p ^ k) = X ^ (p ^ k) - 1 := by
  rw [sub_pow_char_pow, one_pow]

theorem X_sub_one_pow_pred (k : ℕ) :
    ((X : K[X]) - 1) ^ (p ^ k - 1) = ∑ i ∈ Finset.range (p ^ k), X ^ i := by
  have hX : (X : K[X]) - 1 ≠ 0 := X_sub_C_ne_zero 1
  have h1 : (∑ i ∈ Finset.range (p ^ k), (X : K[X]) ^ i) * (X - 1) = X ^ (p ^ k) - 1 :=
    geom_sum_mul X _
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have h2 : ((X : K[X]) - 1) ^ (p ^ k - 1) * (X - 1) = X ^ (p ^ k) - 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpk, X_sub_one_pow_char_pow]
  exact mul_right_cancel₀ hX (h2.trans h1.symm)

theorem sub_one_pow_char_pow (a : Module.End K V) (k : ℕ) :
    (a - 1) ^ (p ^ k) = a ^ (p ^ k) - 1 := by
  have := congrArg (aeval a) (X_sub_one_pow_char_pow (K := K) (p := p) k)
  simpa using this

theorem sub_one_pow_pred (a : Module.End K V) (k : ℕ) :
    (a - 1) ^ (p ^ k - 1) = ∑ i ∈ Finset.range (p ^ k), a ^ i := by
  have := congrArg (aeval a) (X_sub_one_pow_pred (K := K) (p := p) k)
  simpa using this

end CharP

section Joint

theorem units_conj_pow {R : Type*} [Monoid R] (u : Rˣ) (M : R) (m : ℕ) :
    ((u : R) * M * ((u⁻¹ : Rˣ) : R)) ^ m = (u : R) * M ^ m * ((u⁻¹ : Rˣ) : R) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, mul_one, Units.mul_inv]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc ((u⁻¹ : Rˣ) : R), Units.inv_mul, one_mul]

theorem inv_mul_mul_mem_of_mem_normalizer {G : Type*} [Group G] {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (A : Set G)) {a : G} (ha : a ∈ A) : x⁻¹ * a * x ∈ A := by
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hx) a).1 ha
  rwa [inv_inv] at this

@[expose] def jointGen (A : Subgroup (Module.End K V)ˣ) (χ : A → K) : Submodule K V :=
  ⨅ a : A, ((a : (Module.End K V)ˣ) : Module.End K V).maxGenEigenspace (χ a)

theorem mem_jointGen {A : Subgroup (Module.End K V)ˣ} {χ : A → K} {v : V} :
    v ∈ jointGen A χ ↔ ∀ a : A, ∃ k : ℕ,
      ((((a : (Module.End K V)ˣ) : Module.End K V) - χ a • 1) ^ k) v = 0 := by
  rw [jointGen, Module.End.mem_iInf_maxGenEigenspace_iff]

@[expose] def twistChar {A : Subgroup (Module.End K V)ˣ} (x : (Module.End K V)ˣ)
    (hx : x ∈ Subgroup.normalizer (A : Set (Module.End K V)ˣ)) (χ : A → K) : A → K := fun a =>
  χ ⟨x⁻¹ * a * x, inv_mul_mul_mem_of_mem_normalizer hx a.2⟩

theorem twistChar_apply {A : Subgroup (Module.End K V)ˣ} (x : (Module.End K V)ˣ)
    (hx : x ∈ Subgroup.normalizer (A : Set (Module.End K V)ˣ)) (χ : A → K) (a : A)
    (h : x⁻¹ * a * x ∈ A) :
    twistChar x hx χ a = χ ⟨x⁻¹ * a * x, h⟩ :=
  rfl

theorem apply_mem_jointGen_twist {A : Subgroup (Module.End K V)ˣ} (x : (Module.End K V)ˣ)
    (hx : x ∈ Subgroup.normalizer (A : Set (Module.End K V)ˣ)) {χ : A → K} {v : V}
    (hv : v ∈ jointGen A χ) :
    (x : Module.End K V) v ∈ jointGen A (twistChar x hx χ) := by
  rw [mem_jointGen] at hv ⊢
  intro a
  have ha : x⁻¹ * a * x ∈ A := inv_mul_mul_mem_of_mem_normalizer hx a.2
  obtain ⟨k, hk⟩ := hv ⟨x⁻¹ * a * x, ha⟩
  refine ⟨k, ?_⟩
  have h1 : (x : Module.End K V) * ((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) = 1 :=
    Units.mul_inv x
  have h2 : (((x⁻¹ * a * x : (Module.End K V)ˣ)) : Module.End K V) =
      ((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) * ((a : (Module.End K V)ˣ) :
        Module.End K V) * (x : Module.End K V) := by
    rw [Units.val_mul, Units.val_mul]
  set M := (((x⁻¹ * a * x : (Module.End K V)ˣ)) : Module.End K V) - χ ⟨x⁻¹ * a * x, ha⟩ • 1
    with hMdef
  have hconj : ((a : (Module.End K V)ˣ) : Module.End K V) - twistChar x hx χ a • 1 =
      (x : Module.End K V) * M * ((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) := by
    rw [hMdef, twistChar_apply x hx χ a ha, h2, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      mul_one, h1]
    congr 1
    simp only [mul_assoc]
    rw [h1, mul_one, ← mul_assoc, h1, one_mul]
  rw [hconj, units_conj_pow, Module.End.mul_apply, Module.End.mul_apply,
    ← Module.End.mul_apply ((x⁻¹ : (Module.End K V)ˣ) : Module.End K V), Units.inv_mul,
    Module.End.one_apply, hMdef, hk, map_zero]

end Joint

section Block

variable {A : Subgroup (Module.End K V)ˣ}

theorem iterate_twistChar (x : (Module.End K V)ˣ)
    (hx : x ∈ Subgroup.normalizer (A : Set (Module.End K V)ˣ)) (i : ℕ) (χ : A → K) :
    (twistChar x hx)^[i] χ = twistChar (x ^ i) (pow_mem hx i) χ := by
  induction i generalizing χ with
  | zero =>
    funext a
    simp only [Function.iterate_zero, id_eq, twistChar, pow_zero, inv_one, one_mul, mul_one]
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    funext a
    simp only [twistChar]
    congr 1
    apply Subtype.ext
    simp only [pow_succ, mul_inv_rev, mul_assoc]

theorem iSupIndep_jointGen (hA : ∀ a b : A, Commute ((a : (Module.End K V)ˣ) : Module.End K V)
    ((b : (Module.End K V)ˣ) : Module.End K V)) : iSupIndep (jointGen (K := K) A) := by
  refine Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (f := fun a : A => ((a : (Module.End K V)ˣ) : Module.End K V)) fun a b μ => ?_
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hA b a) μ

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem sub_one_pow_ne_zero_of_jointGen (hA : ∀ a b : A, Commute
    ((a : (Module.End K V)ˣ) : Module.End K V) ((b : (Module.End K V)ˣ) : Module.End K V))
    (x : (Module.End K V)ˣ) (hx : x ∈ Subgroup.normalizer (A : Set (Module.End K V)ˣ))
    {χ : A → K} {k : ℕ} (hper : Function.minimalPeriod (twistChar x hx) χ = p ^ k) {u : V}
    (hu : u ∈ jointGen A χ) {j : ℕ}
    (hj : (((x : Module.End K V) ^ (p ^ k) - 1 : Module.End K V) ^ j) u ≠ 0) :
    ((x : Module.End K V) - 1) ^ (p ^ k * (j + 1) - 1) ≠ 0 := by
  classical
  set Φ := twistChar x hx with hΦ
  have hpk : 0 < p ^ k := pow_pos (Fact.out : p.Prime).pos k
  have hfix : Φ^[p ^ k] χ = χ := by
    rw [← hper]
    exact Function.iterate_minimalPeriod
  have hy : ∀ v ∈ jointGen A χ, ((x : Module.End K V) ^ (p ^ k)) v ∈ jointGen A χ := by
    intro v hv
    have := apply_mem_jointGen_twist (x ^ (p ^ k)) (pow_mem hx _) hv
    rwa [← iterate_twistChar, hfix, Units.val_pow_eq_pow_val] at this
  have hyw : ∀ m, ∀ v ∈ jointGen A χ,
      (((x : Module.End K V) ^ (p ^ k) - 1 : Module.End K V) ^ m) v ∈ jointGen A χ := by
    intro m
    induction m with
    | zero => intro v hv; simpa using hv
    | succ m ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
      exact Submodule.sub_mem _ (hy _ (ih v hv)) (ih v hv)
  set w := (((x : Module.End K V) ^ (p ^ k) - 1 : Module.End K V) ^ j) u with hwdef
  have hwmem : w ∈ jointGen A χ := hyw j u hu
  have hmem : ∀ i : Fin (p ^ k), ((x : Module.End K V) ^ (i : ℕ)) w ∈
      jointGen A (Φ^[(i : ℕ)] χ) := fun i => by
    have := apply_mem_jointGen_twist (x ^ (i : ℕ)) (pow_mem hx _) hwmem
    rwa [← iterate_twistChar, Units.val_pow_eq_pow_val] at this
  have hne : ∀ i : Fin (p ^ k), ((x : Module.End K V) ^ (i : ℕ)) w ≠ 0 := fun i h => by
    apply hj
    have hinj : Function.Injective ((x : Module.End K V) ^ (i : ℕ)) := by
      rw [← Units.val_pow_eq_pow_val]
      exact (Module.End.isUnit_iff _).1 (Units.isUnit _) |>.1
    exact hinj (by rw [h, map_zero])
  have hind : iSupIndep fun i : Fin (p ^ k) => jointGen A (Φ^[(i : ℕ)] χ) := by
    refine (iSupIndep_jointGen hA).comp fun i i' h => Fin.ext ?_
    have hi : (i : ℕ) < Function.minimalPeriod Φ χ := by rw [hper]; exact i.2
    have hi' : (i' : ℕ) < Function.minimalPeriod Φ χ := by rw [hper]; exact i'.2
    exact Function.iterate_injOn_Iio_minimalPeriod hi hi' h
  have hli := hind.linearIndependent _ hmem hne
  have hsum : ∑ i : Fin (p ^ k), ((x : Module.End K V) ^ (i : ℕ)) w ≠ 0 := by
    intro h
    have := linearIndependent_iff'.1 hli Finset.univ (fun _ => 1) (by simpa using h)
      ⟨0, hpk⟩ (Finset.mem_univ _)
    exact one_ne_zero this
  intro h0
  apply hsum
  have hsplit : p ^ k * (j + 1) - 1 = (p ^ k - 1) + p ^ k * j := by
    rw [mul_add, mul_one]
    omega
  have h1 := congrArg (fun f : Module.End K V => f u) h0
  simp only [LinearMap.zero_apply] at h1
  rw [hsplit, pow_add, pow_mul, sub_one_pow_char_pow (p := p), Module.End.mul_apply,
    ← hwdef, sub_one_pow_pred (p := p), LinearMap.sum_apply] at h1
  rw [← h1, Finset.sum_range]

end Block

section Abelian

variable {A : Subgroup (Module.End K V)ˣ} {p : ℕ} [Fact p.Prime] [CharP K p]

theorem isSemisimple_of_pow_eq_one {a : Module.End K V} {N : ℕ} (hN : a ^ N = 1)
    (hNp : (N : K) ≠ 0) : a.IsSemisimple := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ N - C 1) ?_ ?_
  · exact (separable_X_pow_sub_C 1 hNp one_ne_zero).squarefree
  · simp [hN]

theorem natCast_pow_ne_zero_of_ne {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (e : ℕ) :
    ((q ^ e : ℕ) : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K p]
  intro h
  exact hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).1
    ((Fact.out : p.Prime).dvd_of_dvd_pow h)).symm

theorem apply_eq_smul_of_mem_jointGen {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hAq : IsPGroup q A)
    {χ : A → K} {v : V} (hv : v ∈ jointGen A χ) (a : A) :
    ((a : (Module.End K V)ˣ) : Module.End K V) v = χ a • v := by
  obtain ⟨e, he⟩ := hAq a
  have hsemi : (((a : (Module.End K V)ˣ) : Module.End K V)).IsSemisimple := by
    refine isSemisimple_of_pow_eq_one (N := q ^ e) ?_ (natCast_pow_ne_zero_of_ne hq hqp e)
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, he]
    rfl
  have hmem : v ∈ (((a : (Module.End K V)ˣ) : Module.End K V)).maxGenEigenspace (χ a) :=
    (iInf_le _ a : jointGen A χ ≤ _) hv
  rw [hsemi.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hmem
  exact Module.End.mem_eigenspace_iff.1 hmem

theorem iSup_jointGen_eq_top [IsAlgClosed K] [FiniteDimensional K V]
    (hA : ∀ a b : A, Commute ((a : (Module.End K V)ˣ) : Module.End K V)
      ((b : (Module.End K V)ˣ) : Module.End K V)) :
    ⨆ χ : A → K, jointGen A χ = ⊤ :=
  Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun a : A => ((a : (Module.End K V)ˣ) : Module.End K V)) (fun a b _ => hA a b)
    fun _ => Module.End.iSup_maxGenEigenspace_eq_top _

theorem iterate_twistChar_of_pow_eq_one (x : (Module.End K V)ˣ)
    (hx : x ∈ Subgroup.normalizer (A : Set (Module.End K V)ˣ)) {N : ℕ} (hxN : x ^ N = 1)
    (χ : A → K) : (twistChar x hx)^[N] χ = χ := by
  rw [iterate_twistChar]
  funext a
  simp only [twistChar]
  congr 1
  apply Subtype.ext
  simp [hxN]

theorem sub_one_pow_ne_zero_of_abelian [IsAlgClosed K] [FiniteDimensional K V]
    (hA : ∀ a b : A, Commute ((a : (Module.End K V)ˣ) : Module.End K V)
      ((b : (Module.End K V)ˣ) : Module.End K V)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hAq : IsPGroup q A) (x : (Module.End K V)ˣ)
    (hx : x ∈ Subgroup.normalizer (A : Set (Module.End K V)ˣ)) {n : ℕ} (hn : 1 ≤ n)
    (hxn : x ^ (p ^ n) = 1) (hz : ∃ a ∈ A, x ^ (p ^ (n - 1)) * a ≠ a * x ^ (p ^ (n - 1))) :
    ((x : Module.End K V) - 1) ^ (p ^ n - 1) ≠ 0 := by
  classical
  set Φ := twistChar x hx with hΦ
  set z := x ^ (p ^ (n - 1)) with hzdef
  have hzA : z ∈ Subgroup.normalizer (A : Set (Module.End K V)ˣ) := pow_mem hx _
  obtain ⟨χ, hχne, hχz⟩ : ∃ χ : A → K, jointGen A χ ≠ ⊥ ∧ Φ^[p ^ (n - 1)] χ ≠ χ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, hza⟩ := hz
    apply hza
    have hconj : ((z⁻¹ * a * z : (Module.End K V)ˣ) : Module.End K V) =
        (a : Module.End K V) := by
      have hle : ⨆ χ : A → K, jointGen A χ ≤ LinearMap.eqLocus
          ((z⁻¹ * a * z : (Module.End K V)ˣ) : Module.End K V) (a : Module.End K V) := by
        refine iSup_le fun χ => ?_
        by_cases hbot : jointGen A χ = ⊥
        · rw [hbot]
          exact bot_le
        intro v hv
        have hfix := hcon χ hbot
        have h1 := apply_eq_smul_of_mem_jointGen hq hqp hAq hv
          ⟨z⁻¹ * a * z, inv_mul_mul_mem_of_mem_normalizer hzA ha⟩
        have h2 := apply_eq_smul_of_mem_jointGen hq hqp hAq hv ⟨a, ha⟩
        change ((z⁻¹ * a * z : (Module.End K V)ˣ) : Module.End K V) v =
          (a : Module.End K V) v
        rw [h1, h2]
        congr 1
        have h3 : twistChar z hzA χ ⟨a, ha⟩ = χ ⟨a, ha⟩ := by
          rw [show twistChar z hzA χ = Φ^[p ^ (n - 1)] χ from (iterate_twistChar x hx _ χ).symm,
            hfix]
        exact h3
      rw [iSup_jointGen_eq_top hA] at hle
      exact LinearMap.ext fun v => hle (Submodule.mem_top (x := v))
    have := Units.ext hconj
    calc z * a = z * (z⁻¹ * a * z) := by rw [this]
      _ = a * z := by group
  have hper : Function.minimalPeriod Φ χ = p ^ n := by
    have hdvd : Function.minimalPeriod Φ χ ∣ p ^ n :=
      Function.IsPeriodicPt.minimalPeriod_dvd (iterate_twistChar_of_pow_eq_one x hx hxn χ)
    obtain ⟨a, ha, heq⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
    rcases Nat.lt_or_ge a n with hlt | hge
    · exfalso
      apply hχz
      have : Function.IsPeriodicPt Φ (Function.minimalPeriod Φ χ) χ :=
        Function.isPeriodicPt_minimalPeriod Φ χ
      rw [heq] at this
      have hdvd' : p ^ a ∣ p ^ (n - 1) := pow_dvd_pow p (by omega)
      obtain ⟨c, hc⟩ := hdvd'
      rw [hc]
      exact (this.mul_const c).eq
    · rw [heq, le_antisymm ha hge]
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχne
  have := sub_one_pow_ne_zero_of_jointGen (p := p) hA x hx hper hu (j := 0) (by simpa using hu0)
  simpa using this

end Abelian

end CFSG.GroupTheory.HallHigmanB

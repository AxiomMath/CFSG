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
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Module

variable {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

theorem exists_isPrimitiveRoot_of_isAlgClosed [IsAlgClosed E] {m : ℕ} (hm : (m : E) ≠ 0) :
    ∃ ζ : E, IsPrimitiveRoot ζ m := by
  haveI : NeZero (m : E) := ⟨hm⟩
  haveI : NeZero m := .of_neZero_natCast E
  exact HasEnoughRootsOfUnity.exists_primitiveRoot E m

theorem iSupIndep_eigenspace_pow {t : Module.End E V} {m : ℕ} {ζ : E} (hζ : IsPrimitiveRoot ζ m) :
    iSupIndep fun k : Fin m => t.eigenspace (ζ ^ (k : ℕ)) := by
  have hinj : Function.Injective fun k : Fin m => ζ ^ (k : ℕ) := fun a b hab =>
    Fin.ext (hζ.pow_inj a.isLt b.isLt hab)
  exact (Module.End.eigenspaces_iSupIndep t).comp hinj

theorem eigen_pow_apply_of_mem {t' : Module.End E V} {μ : E} {v : V}
    (hv : v ∈ t'.eigenspace μ) (s : ℕ) : (t' ^ s) v = μ ^ s • v := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ' t' s, Module.End.mul_apply, ih, map_smul, Module.End.mem_eigenspace_iff.mp hv,
      smul_smul, pow_succ μ s]

theorem iSup_eigenspace_pow_eq_top [IsAlgClosed E] [FiniteDimensional E V] {t : Module.End E V}
    {m : ℕ} {ζ : E} (hζ : IsPrimitiveRoot ζ m) (hm : (m : E) ≠ 0) (ht : t ^ m = 1) :
    ⨆ k : Fin m, t.eigenspace (ζ ^ (k : ℕ)) = ⊤ := by
  haveI : NeZero (m : E) := ⟨hm⟩
  haveI : NeZero m := .of_neZero_natCast E
  have hsep : (Polynomial.X ^ m - Polynomial.C (1 : E)).Separable :=
    Polynomial.separable_X_pow_sub_C (1 : E) hm one_ne_zero
  have hss : t.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [ht])
  refine le_antisymm le_top ?_
  rw [← hss.iSup_eigenspace_eq_top]
  refine iSup_le fun μ => ?_
  by_cases hμ : μ ^ m = 1
  · obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
    exact le_iSup (fun k : Fin m => t.eigenspace (ζ ^ (k : ℕ))) ⟨k, hk⟩
  · have hbot : t.eigenspace μ = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have h1 := eigen_pow_apply_of_mem hv m
      rw [ht, Module.End.one_apply] at h1
      have h2 : (1 - μ ^ m) • v = 0 := by
        rw [sub_smul, one_smul, ← h1, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact absurd (sub_eq_zero.mp h3).symm hμ
      · rw [Submodule.mem_bot]
        exact h3
    rw [hbot]
    exact bot_le

theorem sum_finrank_eigenspace_pow [IsAlgClosed E] [FiniteDimensional E V] {t : Module.End E V}
    {m : ℕ} {ζ : E} (hζ : IsPrimitiveRoot ζ m) (hm : (m : E) ≠ 0) (ht : t ^ m = 1) :
    ∑ k : Fin m, finrank E (t.eigenspace (ζ ^ (k : ℕ))) = finrank E V := by
  let A : Fin m → Submodule E V := fun k => t.eigenspace (ζ ^ (k : ℕ))
  have hds : DirectSum.IsInternal A :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (iSupIndep_eigenspace_pow hζ) (iSup_eigenspace_pow_eq_top hζ hm ht)
  have h := (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hds).finrank_eq
  rw [Module.finrank_directSum] at h
  exact h

theorem exists_eigenspace_ne_bot_of_ne_one [IsAlgClosed E] [FiniteDimensional E V]
    {t : Module.End E V} {m : ℕ} {ζ : E} (hζ : IsPrimitiveRoot ζ m) (hm : (m : E) ≠ 0)
    (ht : t ^ m = 1) (ht1 : t ≠ 1) :
    ∃ k : Fin m, (k : ℕ) ≠ 0 ∧ t.eigenspace (ζ ^ (k : ℕ)) ≠ ⊥ := by
  by_contra hcon
  push_neg at hcon
  apply ht1
  have htop := iSup_eigenspace_pow_eq_top hζ hm ht
  have hle : (⨆ k : Fin m, t.eigenspace (ζ ^ (k : ℕ))) ≤ t.eigenspace 1 := by
    refine iSup_le fun k => ?_
    by_cases h0 : (k : ℕ) = 0
    · rw [h0, pow_zero]
    · rw [hcon k h0]
      exact bot_le
  have hv' : ∀ v : V, v ∈ (⨆ k : Fin m, t.eigenspace (ζ ^ (k : ℕ))) := fun v => by
    rw [htop]
    exact Submodule.mem_top
  ext v
  have hv : v ∈ t.eigenspace 1 := hle (hv' v)
  rw [Module.End.mem_eigenspace_iff, one_smul] at hv
  simp [hv]

theorem map_mem_eigenspace_of_mul_eq {t t' g : Module.End E V} (h : g * t = t' * g) {μ : E}
    {v : V} (hv : v ∈ t.eigenspace μ) : g v ∈ t'.eigenspace μ := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h2 : t' (g v) = g (t v) := by
    rw [← Module.End.mul_apply, ← h, Module.End.mul_apply]
  rw [h2, hv, map_smul]

theorem mem_eigenspace_of_pow_eq {t t' : Module.End E V} {s : ℕ} (h : t' ^ s = t) {μ : E}
    {v : V} (hv : v ∈ t'.eigenspace μ) : v ∈ t.eigenspace (μ ^ s) := by
  subst h
  rw [Module.End.mem_eigenspace_iff]
  exact eigen_pow_apply_of_mem hv s

theorem finrank_le_of_mapsTo [FiniteDimensional E V] {W W' : Submodule E V} {g : Module.End E V}
    (hg : Function.Injective g) (h : ∀ v ∈ W, g v ∈ W') : finrank E W ≤ finrank E W' := by
  have hinj : Function.Injective (g.restrict h) := by
    intro a b hab
    have hab' : g (a : V) = g (b : V) := congrArg Subtype.val hab
    exact Subtype.ext (hg hab')
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem finrank_iterate_eq_of_cycle [FiniteDimensional E V] {ι : Type*} (W : ι → Submodule E V)
    (σ : ι → ι) {g : Module.End E V} (hg : Function.Injective g)
    (hmap : ∀ i, ∀ v ∈ W i, g v ∈ W (σ i)) (i : ι) {N : ℕ} (hN : 0 < N) (hcyc : σ^[N] i = i)
    (n : ℕ) : finrank E (W (σ^[n] i)) = finrank E (W i) := by
  have hstep : ∀ j : ℕ, finrank E (W (σ^[j] i)) ≤ finrank E (W (σ^[j + 1] i)) := fun j => by
    have hs : σ^[j + 1] i = σ (σ^[j] i) := Function.iterate_succ_apply' σ j i
    rw [hs]
    exact finrank_le_of_mapsTo hg (hmap (σ^[j] i))
  have hmono := monotone_nat_of_le_succ (f := fun j => finrank E (W (σ^[j] i))) hstep
  have hper : σ^[N * n] i = i := by
    rw [Function.iterate_mul, Function.iterate_fixed hcyc]
  have h0 : finrank E (W i) ≤ finrank E (W (σ^[n] i)) := hmono (Nat.zero_le n)
  have h1 : finrank E (W (σ^[n] i)) ≤ finrank E (W (σ^[N * n] i)) :=
    hmono (Nat.le_mul_of_pos_left n hN)
  rw [hper] at h1
  exact le_antisymm h1 h0

theorem pow_finrank_eq_one_of_commutator [FiniteDimensional E V] {c : E}
    {x y w : Module.End E V} (hx : IsUnit x) (hy : IsUnit y) (hw : w * w = 1)
    (h : x * y = (c • w) * (y * x)) : c ^ (2 * finrank E V) = 1 := by
  have hd := congrArg (LinearMap.det) h
  rw [map_mul, map_mul, map_mul, LinearMap.det_smul] at hd
  have hu : IsUnit (LinearMap.det y * LinearMap.det x) :=
    (hy.map LinearMap.det).mul (hx.map LinearMap.det)
  have hD : c ^ finrank E V * LinearMap.det w = 1 := by
    apply hu.mul_right_cancel
    rw [one_mul, ← hd, mul_comm (LinearMap.det x)]
  have hdw : LinearMap.det w * LinearMap.det w = 1 := by
    rw [← map_mul, hw, map_one]
  calc c ^ (2 * finrank E V) = (c ^ finrank E V) ^ 2 := by rw [← pow_mul, mul_comm]
    _ = (c ^ finrank E V) ^ 2 * (LinearMap.det w * LinearMap.det w) := by rw [hdw, mul_one]
    _ = (c ^ finrank E V * LinearMap.det w) ^ 2 := by ring
    _ = 1 := by rw [hD, one_pow]

end CFSG.ComponentClassification.CatFC.KGHS3

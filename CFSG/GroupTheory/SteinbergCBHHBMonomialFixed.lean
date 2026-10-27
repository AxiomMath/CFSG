module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Module

variable {K : Type*} [Field K]

section Monomial

variable {M X : Type*} [AddCommGroup M] [Module K M] [Fintype X] [DecidableEq X]

theorem repr_apply_perm_of_fixed (b : Basis X K M) (T : Module.End K M) (π : Equiv.Perm X)
    (c : X → K) (hT : ∀ x, T (b x) = c x • b (π x)) {φ : M} (hφ : T φ = φ) (x : X) :
    b.repr φ (π x) = c x * b.repr φ x := by
  have h1 : T φ = ∑ y, b.repr φ y • (c y • b (π y)) := by
    conv_lhs => rw [← b.sum_repr φ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, hT]
  have h2 := congrArg (fun v => b.repr v (π x)) h1
  simp only [hφ, map_sum, map_smul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, π.injective.eq_iff, smul_eq_mul] at h2
  rw [h2, Finset.sum_eq_single x (fun y _ hy => by rw [ite_eq_right hy, mul_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ x) h), ite_eq_left rfl, mul_one, mul_comm]

@[expose] def fixedSupported (b : Basis X K M) (T : Module.End K M) (Y : Finset X) :
    Submodule K M :=
  LinearMap.ker (T - 1) ⊓ ⨅ x ∈ (Finset.univ \ Y), LinearMap.ker (b.coord x)

theorem mem_fixedSupported {b : Basis X K M} {T : Module.End K M} {Y : Finset X} {φ : M} :
    φ ∈ fixedSupported b T Y ↔ T φ = φ ∧ ∀ x, x ∉ Y → b.repr φ x = 0 := by
  simp only [fixedSupported, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero, Submodule.mem_iInf, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Basis.coord_apply]

theorem finrank_le_finrank_inf_ker_add_one [FiniteDimensional K M] (U : Submodule K M)
    (f : Module.Dual K M) : finrank K U ≤ finrank K (U ⊓ LinearMap.ker f : Submodule K M) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker f)
  have h2 : finrank K (U ⊔ LinearMap.ker f : Submodule K M) ≤ finrank K M :=
    Submodule.finrank_le _
  have h3 := LinearMap.finrank_range_add_finrank_ker f
  have h4 : finrank K (LinearMap.range f) ≤ 1 := by
    calc finrank K (LinearMap.range f) ≤ finrank K K := Submodule.finrank_le _
      _ = 1 := finrank_self K
  omega

theorem mul_finrank_ker_sub_one_le [FiniteDimensional K M] (b : Basis X K M)
    (T : Module.End K M) (π : Equiv.Perm X) (c : X → K) (hT : ∀ x, T (b x) = c x • b (π x))
    {P : ℕ} (hP : 0 < P) (e : X) (he : π e = e) (hπP : ∀ x, (π ^ P) x = x)
    (hfree : ∀ x, x ≠ e → ∀ i j, i < P → j < P → (π ^ i) x = (π ^ j) x → i = j) :
    P * finrank K (LinearMap.ker (T - 1)) ≤ Fintype.card X - 1 + P := by
  classical
  have hpow_e : ∀ i, (π ^ i) e = e := fun i => by
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, he]
  have key : ∀ n, ∀ Y : Finset X, Y.card = n → e ∈ Y → (∀ y ∈ Y, π y ∈ Y) →
      P * finrank K (fixedSupported b T Y) ≤ Y.card - 1 + P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro Y hYn heY hYπ
    by_cases hY : ∀ y ∈ Y, y = e
    ·
      have hle : fixedSupported b T Y ≤ K ∙ b e := by
        intro φ hφ
        rw [mem_fixedSupported] at hφ
        rw [Submodule.mem_span_singleton]
        refine ⟨b.repr φ e, ?_⟩
        conv_rhs => rw [← b.sum_repr φ]
        rw [Finset.sum_eq_single e (fun x _ hx => by
          rw [hφ.2 x (fun hxY => hx (hY x hxY)), zero_smul])
          (fun h => absurd (Finset.mem_univ e) h)]
      have h1 : finrank K (fixedSupported b T Y) ≤ 1 :=
        (Submodule.finrank_mono hle).trans (finrank_span_singleton (b.ne_zero e)).le
      have h2 : 1 ≤ Y.card := Finset.card_pos.2 ⟨e, heY⟩
      nlinarith
    push Not at hY
    obtain ⟨x₀, hx₀Y, hx₀e⟩ := hY
    set O := (Finset.range P).image fun i => (π ^ i) x₀ with hOdef
    have hOcard : O.card = P := by
      rw [hOdef, Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      exact hfree x₀ hx₀e i j (by simpa using hi) (by simpa using hj) hij
    have hpowY : ∀ i, (π ^ i) x₀ ∈ Y := fun i => by
      induction i with
      | zero => simpa using hx₀Y
      | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hYπ _ ih
    have hOY : O ⊆ Y := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hpowY i
    have heO : e ∉ O := by
      intro h
      obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 h
      have hi' : i < P := by simpa using hi
      have := congrArg (π ^ (P - i)) hie
      rw [← Equiv.Perm.mul_apply, ← pow_add, show P - i + i = P by omega, hπP, hpow_e] at this
      exact hx₀e this
    set Y' := Y \ O with hY'def
    have hY'card : Y'.card = Y.card - P := by
      rw [hY'def, Finset.card_sdiff_of_subset hOY, hOcard]
    have hPY : P ≤ Y.card := hOcard ▸ Finset.card_le_card hOY
    have heY' : e ∈ Y' := Finset.mem_sdiff.2 ⟨heY, heO⟩
    have hY'π : ∀ y ∈ Y', π y ∈ Y' := by
      intro y hy
      obtain ⟨hyY, hyO⟩ := Finset.mem_sdiff.1 hy
      refine Finset.mem_sdiff.2 ⟨hYπ y hyY, fun h => hyO ?_⟩
      obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 h
      have hi' : i < P := by simpa using hi
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · refine Finset.mem_image.2 ⟨P - 1, by simp; omega, π.injective ?_⟩
        rw [← Equiv.Perm.mul_apply, ← pow_succ', show P - 1 + 1 = P by omega, hπP, ← hie]
        rfl
      · refine Finset.mem_image.2 ⟨i - 1, by simp; omega, π.injective ?_⟩
        rw [← Equiv.Perm.mul_apply, ← pow_succ', show i - 1 + 1 = i by omega, hie]
    have hIH := ih Y'.card (by omega) Y' rfl heY' hY'π
    have hker : fixedSupported b T Y ⊓ LinearMap.ker (b.coord x₀) ≤ fixedSupported b T Y' := by
      intro φ hφ
      obtain ⟨hφY, hφ0⟩ := Submodule.mem_inf.1 hφ
      rw [mem_fixedSupported] at hφY ⊢
      rw [LinearMap.mem_ker, Basis.coord_apply] at hφ0
      have hpow0 : ∀ i, b.repr φ ((π ^ i) x₀) = 0 := fun i => by
        induction i with
        | zero => simpa using hφ0
        | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply,
            repr_apply_perm_of_fixed b T π c hT hφY.1, ih, mul_zero]
      refine ⟨hφY.1, fun x hx => ?_⟩
      by_cases hxY : x ∈ Y
      · have hxO : x ∈ O := by
          by_contra h
          exact hx (Finset.mem_sdiff.2 ⟨hxY, h⟩)
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hxO
        exact hpow0 i
      · exact hφY.2 x hxY
    have h1 := finrank_le_finrank_inf_ker_add_one (fixedSupported b T Y) (b.coord x₀)
    have h2 := Submodule.finrank_mono hker
    have h3 : 1 ≤ Y'.card := Finset.card_pos.2 ⟨e, heY'⟩
    calc P * finrank K (fixedSupported b T Y)
        ≤ P * (finrank K (fixedSupported b T Y') + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = P * finrank K (fixedSupported b T Y') + P := by ring
      _ ≤ Y'.card - 1 + P + P := by omega
      _ = Y.card - 1 + P := by omega
  have huniv : fixedSupported b T Finset.univ = LinearMap.ker (T - 1) := by
    ext φ
    rw [mem_fixedSupported, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero]
    simp
  have := key _ Finset.univ rfl (Finset.mem_univ e) fun y _ => Finset.mem_univ _
  rwa [huniv, Finset.card_univ] at this

end Monomial

section Dedekind

theorem linearIndependent_of_ne_monoidHom {G M ι : Type*} [Monoid G] [AddCommGroup M]
    [Module K M] (ρ : G →* Module.End K M) (v : ι → M) (χ : ι → G →* K)
    (hχ : Function.Injective χ) (hv : ∀ i, v i ≠ 0) (hρ : ∀ g i, ρ g (v i) = χ i g • v i) :
    LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual K M, ℓ (v i) ≠ 0 := by
    by_contra h
    push Not at h
    exact hv i ((Module.forall_dual_apply_eq_zero_iff K _).1 h)
  have hD := (linearIndependent_monoidHom G K).comp χ hχ
  rw [linearIndependent_iff'] at hD
  have hsum : ∑ j ∈ s, (g j * ℓ (v j)) • (fun x : G => (χ j : G →* K) x) = 0 := by
    funext x
    have h1 := congrArg (fun w => ℓ (ρ x w)) hg
    simp only [map_sum, map_smul, hρ, map_zero, smul_eq_mul] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := hD s (fun j => g j * ℓ (v j)) hsum i hi
  exact (mul_eq_zero.1 this).resolve_right hℓ

end Dedekind

end CFSG.GroupTheory.HallHigmanB

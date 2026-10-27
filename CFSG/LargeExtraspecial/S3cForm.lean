module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.LargeExtraspecial

open Module

theorem map_smul_of_map_add_zmod2 {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    {f : A → ZMod 2} (hf : ∀ x y, f (x + y) = f x + f y) (c : ZMod 2) (x : A) :
    f (c • x) = c * f x := by
  have h0 : f 0 = 0 := by
    have := hf 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide
  rcases hc with rfl | rfl
  · rw [zero_smul, zero_mul, h0]
  · rw [one_smul, one_mul]

theorem zmod2_mul_add_mul_comm (u v : ZMod 2) : u * v + v * u = 0 := by
  revert u v
  decide

variable {K : Type*} [AddCommGroup K]

structure IsAltTrilin (T : K → K → K → ZMod 2) : Prop where
  add_left : ∀ x x' y z, T (x + x') y z = T x y z + T x' y z
  swap₁₂ : ∀ x y z, T x y z = T y x z
  swap₂₃ : ∀ x y z, T x y z = T x z y
  self₁₂ : ∀ x z, T x x z = 0

namespace IsAltTrilin

variable {T : K → K → K → ZMod 2} (h : IsAltTrilin T)
include h

theorem add_mid (x y y' z : K) : T x (y + y') z = T x y z + T x y' z := by
  rw [h.swap₁₂, h.add_left, h.swap₁₂ y, h.swap₁₂ y']

theorem add_right (x y z z' : K) : T x y (z + z') = T x y z + T x y z' := by
  rw [h.swap₂₃, h.add_mid, h.swap₂₃ x z, h.swap₂₃ x z']

theorem self₁₃ (x y : K) : T x y x = 0 := by
  rw [h.swap₂₃, h.self₁₂]

theorem self₂₃ (x y : K) : T x y y = 0 := by
  rw [h.swap₁₂, h.self₁₃]

theorem cyc (x y z : K) : T x y z = T y z x := by
  rw [h.swap₁₂, h.swap₂₃]

variable [Module (ZMod 2) K]

@[expose] def toLin : K →ₗ[ZMod 2] K →ₗ[ZMod 2] K →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y =>
      { toFun := T x y
        map_add' := h.add_right x y
        map_smul' := fun c z => by
          rw [RingHom.id_apply, smul_eq_mul]
          exact map_smul_of_map_add_zmod2 (h.add_right x y) c z })
    (fun x x' y => LinearMap.ext fun z => h.add_left x x' y z)
    (fun c x y => LinearMap.ext fun z => by
      rw [LinearMap.smul_apply, smul_eq_mul]
      exact map_smul_of_map_add_zmod2 (f := fun x => T x y z) (fun x x' => h.add_left x x' y z) c x)
    (fun x y y' => LinearMap.ext fun z => h.add_mid x y y' z)
    (fun c x y => LinearMap.ext fun z => by
      rw [LinearMap.smul_apply, smul_eq_mul]
      exact map_smul_of_map_add_zmod2 (f := fun y => T x y z) (fun y y' => h.add_mid x y y' z) c y)

@[simp] theorem toLin_apply (x y z : K) : h.toLin x y z = T x y z := rfl

theorem radical_of_basis {ι : Type*} (b : Basis ι (ZMod 2) K) {x : K}
    (hx : ∀ j k, T x (b j) (b k) = 0) (y z : K) : T x y z = 0 := by
  have : h.toLin x = 0 := LinearMap.ext_basis b b fun j k => by simpa using hx j k
  simpa using LinearMap.congr_fun₂ this y z

theorem eq_zero_of_basis {ι : Type*} (b : Basis ι (ZMod 2) K)
    (hb : ∀ i j k, T (b i) (b j) (b k) = 0) (x y z : K) : T x y z = 0 := by
  have : h.toLin = 0 := Basis.ext b fun i => LinearMap.ext_basis b b fun j k => by
    simpa using hb i j k
  have h2 := LinearMap.congr_fun₂ this x y
  simpa using LinearMap.congr_fun h2 z

theorem apply_add_four (b₀ b₁ b₂ b₃ y z : K) (c₀ c₁ c₂ c₃ : ZMod 2) :
    T (c₀ • b₀ + c₁ • b₁ + c₂ • b₂ + c₃ • b₃) y z =
      c₀ * T b₀ y z + c₁ * T b₁ y z + c₂ * T b₂ y z + c₃ * T b₃ y z := by
  have e : T (c₀ • b₀ + c₁ • b₁ + c₂ • b₂ + c₃ • b₃) y z =
      h.toLin (c₀ • b₀ + c₁ • b₁ + c₂ • b₂ + c₃ • b₃) y z := rfl
  rw [e]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    toLin_apply]

theorem apply_add_three (b₀ b₁ b₂ y z : K) (c₀ c₁ c₂ : ZMod 2) :
    T (c₀ • b₀ + c₁ • b₁ + c₂ • b₂) y z = c₀ * T b₀ y z + c₁ * T b₁ y z + c₂ * T b₂ y z := by
  have e : T (c₀ • b₀ + c₁ • b₁ + c₂ • b₂) y z = h.toLin (c₀ • b₀ + c₁ • b₁ + c₂ • b₂) y z := rfl
  rw [e]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    toLin_apply]

theorem radical_of_basis_lt {n : ℕ} (b : Basis (Fin n) (ZMod 2) K) {x : K}
    (hx : ∀ j k, j < k → T x (b j) (b k) = 0) (y z : K) : T x y z = 0 := by
  refine h.radical_of_basis b (fun j k => ?_) y z
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · exact hx j k hjk
  · exact h.self₂₃ _ _
  · rw [h.swap₂₃]
    exact hx k j hjk

theorem eq_zero_of_finrank_eq_three [Module.Finite (ZMod 2) K] (hK : finrank (ZMod 2) K = 3)
    {x₀ : K} (hx₀ : x₀ ≠ 0) (hrad : ∀ y z, T x₀ y z = 0) (x y z : K) : T x y z = 0 := by
  set b := Module.finBasisOfFinrankEq (ZMod 2) K hK with hb
  set c := b.equivFun x₀ with hc
  have hx : x₀ = c 0 • b 0 + c 1 • b 1 + c 2 • b 2 := by
    conv_lhs => rw [← b.sum_equivFun x₀]
    rw [Fin.sum_univ_three]
  have key : ∀ j k, T x₀ (b j) (b k) =
      c 0 * T (b 0) (b j) (b k) + c 1 * T (b 1) (b j) (b k) + c 2 * T (b 2) (b j) (b k) := by
    intro j k
    rw [hx]
    exact h.apply_add_three _ _ _ _ _ _ _ _
  set t := T (b 0) (b 1) (b 2) with ht
  have h0 : c 0 * t = 0 := by
    have e := key 1 2
    rw [hrad, h.self₁₂ (b 1), h.self₁₃ (b 2)] at e
    rw [e]
    ring
  have h1 : c 1 * t = 0 := by
    have e := key 0 2
    rw [hrad, h.self₁₂ (b 0), h.self₁₃ (b 2), h.swap₁₂ (b 1)] at e
    rw [e]
    ring
  have h2 : c 2 * t = 0 := by
    have e := key 0 1
    rw [hrad, h.self₁₂ (b 0), h.self₁₃ (b 1), h.cyc (b 2)] at e
    rw [e]
    ring
  have ht0 : t = 0 := by
    by_contra hne
    have hc0 : ∀ i, c i = 0 := by
      intro i
      fin_cases i
      · exact (mul_eq_zero.mp h0).resolve_right hne
      · exact (mul_eq_zero.mp h1).resolve_right hne
      · exact (mul_eq_zero.mp h2).resolve_right hne
    apply hx₀
    rw [hx, hc0 0, hc0 1, hc0 2]
    simp
  refine h.eq_zero_of_basis b (fun i j k => ?_) x y z
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact h.self₁₂ _ _
    | exact h.self₁₃ _ _
    | exact h.self₂₃ _ _
    | exact ht0
    | exact (h.swap₂₃ _ _ _).trans ht0
    | exact (h.swap₁₂ _ _ _).trans ht0
    | exact (h.cyc _ _ _).symm.trans ht0
    | exact (h.cyc _ _ _).trans ht0
    | exact ((h.swap₁₂ _ _ _).trans (h.cyc _ _ _).symm).trans ht0

theorem exists_radical_of_finrank_eq_four [Module.Finite (ZMod 2) K]
    (hK : finrank (ZMod 2) K = 4) : ∃ x, x ≠ 0 ∧ ∀ y z, T x y z = 0 := by
  set b := Module.finBasisOfFinrankEq (ZMod 2) K hK with hb
  set t₁₂₃ := T (b 1) (b 2) (b 3)
  set t₀₂₃ := T (b 0) (b 2) (b 3)
  set t₀₁₃ := T (b 0) (b 1) (b 3)
  set t₀₁₂ := T (b 0) (b 1) (b 2)
  by_cases hall : t₁₂₃ = 0 ∧ t₀₂₃ = 0 ∧ t₀₁₃ = 0 ∧ t₀₁₂ = 0
  · obtain ⟨e₁₂₃, e₀₂₃, e₀₁₃, e₀₁₂⟩ := hall
    refine ⟨b 0, b.ne_zero 0, h.radical_of_basis_lt b fun j k hjk => ?_⟩
    fin_cases j <;> fin_cases k
    all_goals first
      | exact absurd hjk (by decide)
      | exact h.self₁₂ _ _
      | exact h.self₁₃ _ _
      | exact e₀₁₂
      | exact e₀₁₃
      | exact e₀₂₃
  · set x := t₁₂₃ • b 0 + t₀₂₃ • b 1 + t₀₁₃ • b 2 + t₀₁₂ • b 3 with hx
    refine ⟨x, fun hx0 => hall ?_, h.radical_of_basis_lt b fun j k hjk => ?_⟩
    · have hrep : ∀ i, b.repr x i = 0 := fun i => by rw [hx0, map_zero, Finsupp.zero_apply]
      have r0 := hrep 0
      have r1 := hrep 1
      have r2 := hrep 2
      have r3 := hrep 3
      simp only [hx, map_add, map_smul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.single_apply, smul_eq_mul] at r0 r1 r2 r3
      simp at r0 r1 r2 r3
      exact ⟨r0, r1, r2, r3⟩
    · have e01 : T x (b 0) (b 1) = 0 := by
        rw [hx, h.apply_add_four, h.self₁₂ (b 0), h.self₁₃ (b 1), h.cyc (b 2), h.cyc (b 3)]
        simp only [mul_zero, zero_add]
        exact zmod2_mul_add_mul_comm _ _
      have e02 : T x (b 0) (b 2) = 0 := by
        rw [hx, h.apply_add_four, h.self₁₂ (b 0), h.swap₁₂ (b 1), h.self₁₃ (b 2), h.cyc (b 3)]
        simp only [mul_zero, zero_add, add_zero]
        exact zmod2_mul_add_mul_comm _ _
      have e03 : T x (b 0) (b 3) = 0 := by
        rw [hx, h.apply_add_four, h.self₁₂ (b 0), h.swap₁₂ (b 1), h.swap₁₂ (b 2),
          h.self₁₃ (b 3)]
        simp only [mul_zero, zero_add, add_zero]
        exact zmod2_mul_add_mul_comm _ _
      have e12 : T x (b 1) (b 2) = 0 := by
        rw [hx, h.apply_add_four, h.self₁₂ (b 1), h.self₁₃ (b 2), h.cyc (b 3)]
        simp only [mul_zero, add_zero]
        exact zmod2_mul_add_mul_comm _ _
      have e13 : T x (b 1) (b 3) = 0 := by
        rw [hx, h.apply_add_four, h.self₁₂ (b 1), h.swap₁₂ (b 2), h.self₁₃ (b 3)]
        simp only [mul_zero, add_zero]
        exact zmod2_mul_add_mul_comm _ _
      have e23 : T x (b 2) (b 3) = 0 := by
        rw [hx, h.apply_add_four, h.self₁₂ (b 2), h.self₁₃ (b 3)]
        simp only [mul_zero, add_zero]
        exact zmod2_mul_add_mul_comm _ _
      fin_cases j <;> fin_cases k
      all_goals first
        | exact absurd hjk (by decide)
        | exact e01
        | exact e02
        | exact e03
        | exact e12
        | exact e13
        | exact e23

end IsAltTrilin

end CFSG.LargeExtraspecial

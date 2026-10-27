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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {m : ℕ}

structure IsF3Form (f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)) : Prop where
  symm : ∀ x y, f x y = f y x
  nondeg : ∀ x, (∀ y, f x y = 0) → x = 0

namespace F3

theorem three_eq_zero : (3 : ZMod 3) = 0 := by decide

theorem mul_self_of_ne_zero {a : ZMod 3} (h : a ≠ 0) : a * a = 1 := by
  revert a; decide

theorem mul_self_eq_zero_or_one (a : ZMod 3) : a * a = 0 ∨ a * a = 1 := by
  revert a; decide

theorem eq_zero_of_eq_neg {x : Fin m → ZMod 3} (h : x = -x) : x = 0 := by
  have h2 : (2 : ZMod 3) • x = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel x
  calc x = ((2 : ZMod 3) * 2) • x := by rw [show (2 : ZMod 3) * 2 = 1 by decide, one_smul]
    _ = 0 := by rw [mul_smul, h2, smul_zero]

theorem ne_neg_self {x : Fin m → ZMod 3} (h : x ≠ 0) : x ≠ -x := fun h' => h (eq_zero_of_eq_neg h')

variable {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem norm_add (hf : IsF3Form f) (x y : Fin m → ZMod 3) :
    f (x + y) (x + y) = f x x + 2 * f x y + f y y := by
  simp only [map_add, LinearMap.add_apply, hf.symm y x]
  ring

theorem norm_smul (c : ZMod 3) (x : Fin m → ZMod 3) : f (c • x) (c • x) = c * c * f x x := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem norm_add_smul (hf : IsF3Form f) (x y : Fin m → ZMod 3) (c : ZMod 3) :
    f (x + c • y) (x + c • y) = f x x + 2 * c * f x y + c * c * f y y := by
  rw [norm_add hf, norm_smul]
  simp only [map_smul, smul_eq_mul]
  ring

theorem exists_norm_add_smul_eq (hf : IsF3Form f) {x z : Fin m → ZMod 3} (hz : f z z = 0)
    (hxz : f x z ≠ 0) (c : ZMod 3) : ∃ t : ZMod 3, f (x + t • z) (x + t • z) = c := by
  have key : ∀ a b c : ZMod 3, b ≠ 0 → ∃ t, a + 2 * t * b + t * t * 0 = c := by decide
  obtain ⟨t, ht⟩ := key (f x x) (f x z) c hxz
  exact ⟨t, by rw [norm_add_smul hf, hz, ht]⟩

theorem norm_add_pair (hf : IsF3Form f) {v w : Fin m → ZMod 3} (hv : f v v = 1)
    (hw : f w w = 1) : f (v + f v w • w) (v + f v w • w) = 1 := by
  rw [norm_add_smul hf, hv, hw]
  linear_combination (f v w * f v w) * three_eq_zero

@[expose] noncomputable def pairMap (f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)) {k : ℕ}
    (w : Fin k → Fin m → ZMod 3) : (Fin m → ZMod 3) →ₗ[ZMod 3] (Fin k → ZMod 3) :=
  LinearMap.pi fun i => f.flip (w i)

@[simp]
theorem pairMap_apply {k : ℕ} (w : Fin k → Fin m → ZMod 3) (x : Fin m → ZMod 3) (i : Fin k) :
    pairMap f w x i = f x (w i) :=
  rfl

@[expose] noncomputable def perpSub (f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)) {k : ℕ}
    (w : Fin k → Fin m → ZMod 3) : Submodule (ZMod 3) (Fin m → ZMod 3) :=
  LinearMap.ker (pairMap f w)

theorem mem_perpSub {k : ℕ} {w : Fin k → Fin m → ZMod 3} {x : Fin m → ZMod 3} :
    x ∈ perpSub f w ↔ ∀ i, f x (w i) = 0 := by
  rw [perpSub, LinearMap.mem_ker, funext_iff]
  rfl

theorem exists_ne_zero_perp {k : ℕ} (hk : k < m) (w : Fin k → Fin m → ZMod 3) :
    ∃ y, y ≠ 0 ∧ ∀ i, f y (w i) = 0 := by
  have h := LinearMap.ker_ne_bot_of_finrank_lt (f := pairMap f w) (by simpa using hk)
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 h
  exact ⟨y, hy0, mem_perpSub.1 hy⟩

theorem exists_pairings (hf : IsF3Form f) {k : ℕ} {w : Fin k → Fin m → ZMod 3}
    (hw : LinearIndependent (ZMod 3) w) (c : Fin k → ZMod 3) : ∃ x, ∀ i, f x (w i) = c i := by
  suffices h : LinearMap.range (pairMap f w) = ⊤ by
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 h c
    exact ⟨x, fun i => congrFun hx i⟩
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  set a : Fin k → ZMod 3 := fun i => φ fun j => if i = j then 1 else 0
  have hφa : ∀ y, φ y = ∑ i, a i * y i := fun y => by
    rw [LinearMap.pi_apply_eq_sum_univ φ y]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  have hsum : ∑ i, a i • w i = 0 := by
    apply hf.nondeg
    intro y
    rw [hf.symm, map_sum]
    have h0 : φ (pairMap f w y) = 0 := hφ ⟨y, rfl⟩
    rw [hφa] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, pairMap_apply]
  have ha : ∀ i, a i = 0 := Fintype.linearIndependent_iff.1 hw a hsum
  apply hφ0
  refine LinearMap.ext fun y => ?_
  rw [hφa, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [ha i, zero_mul]

theorem perpSub_twoDim (hf : IsF3Form f) {k : ℕ} (hk : k + 1 < m) (w : Fin k → Fin m → ZMod 3) :
    ∀ y ∈ perpSub f w, ∃ y' ∈ perpSub f w, y' ≠ 0 ∧ f y y' = 0 := by
  intro y _
  obtain ⟨y', hy'0, hy'⟩ := exists_ne_zero_perp (f := f) hk (Fin.cons y w)
  refine ⟨y', mem_perpSub.2 fun i => ?_, hy'0, ?_⟩
  · simpa using hy' i.succ
  · rw [hf.symm]; simpa using hy' 0

theorem perpSub_threeDim (hf : IsF3Form f) {k : ℕ} (hk : k + 2 < m)
    (w : Fin k → Fin m → ZMod 3) : ∀ y ∈ perpSub f w, ∀ y' ∈ perpSub f w,
      ∃ y'' ∈ perpSub f w, y'' ≠ 0 ∧ f y y'' = 0 ∧ f y' y'' = 0 := by
  intro y _ y' _
  obtain ⟨y'', h0, h⟩ := exists_ne_zero_perp (f := f) hk (Fin.cons y (Fin.cons y' w))
  refine ⟨y'', mem_perpSub.2 fun i => ?_, h0, ?_, ?_⟩
  · simpa using h i.succ.succ
  · rw [hf.symm]; simpa using h 0
  · rw [hf.symm]; simpa using h 1

theorem nondegOn_of_proj (hf : IsF3Form f) {U : Submodule (ZMod 3) (Fin m → ZMod 3)}
    (p : (Fin m → ZMod 3) → Fin m → ZMod 3) (hpU : ∀ y, p y ∈ U)
    (hp : ∀ x ∈ U, ∀ y, f x (p y) = f x y) : ∀ y ∈ U, y ≠ 0 → ∃ y' ∈ U, f y y' ≠ 0 := by
  intro y hy hy0
  by_contra! h
  exact hy0 (hf.nondeg y fun y' => by rw [← hp y hy y']; exact h _ (hpU y'))

theorem exists_mem_norm_eq (hf : IsF3Form f) {U : Submodule (ZMod 3) (Fin m → ZMod 3)}
    (hnd : ∀ y ∈ U, y ≠ 0 → ∃ y' ∈ U, f y y' ≠ 0)
    (hdim : ∀ y ∈ U, ∃ y' ∈ U, y' ≠ 0 ∧ f y y' = 0) {c : ZMod 3} (hc : c ≠ 0) :
    ∃ y ∈ U, f y y = c := by
  have iso : ∀ z ∈ U, z ≠ 0 → f z z = 0 → ∃ y ∈ U, f y y = c := by
    intro z hzU hz0 hzz
    obtain ⟨y', hy'U, hy'⟩ := hnd z hzU hz0
    obtain ⟨t, ht⟩ := exists_norm_add_smul_eq hf (x := y') hzz (by rwa [hf.symm]) c
    exact ⟨y' + t • z, U.add_mem hy'U (U.smul_mem t hzU), ht⟩
  obtain ⟨y₁, hy₁U, hy₁0, -⟩ := hdim 0 U.zero_mem
  by_cases h1 : f y₁ y₁ = 0
  · exact iso y₁ hy₁U hy₁0 h1
  by_cases h1c : f y₁ y₁ = c
  · exact ⟨y₁, hy₁U, h1c⟩
  obtain ⟨y₂, hy₂U, hy₂0, h12⟩ := hdim y₁ hy₁U
  by_cases h2 : f y₂ y₂ = 0
  · exact iso y₂ hy₂U hy₂0 h2
  by_cases h2c : f y₂ y₂ = c
  · exact ⟨y₂, hy₂U, h2c⟩
  refine ⟨y₁ + y₂, U.add_mem hy₁U hy₂U, ?_⟩
  rw [norm_add hf, h12]
  clear iso
  revert h1 h1c h2 h2c hc
  generalize f y₁ y₁ = a
  generalize f y₂ y₂ = b
  revert a b c
  decide

theorem exists_mem_isotropic (hf : IsF3Form f) {U : Submodule (ZMod 3) (Fin m → ZMod 3)}
    (hnd : ∀ y ∈ U, y ≠ 0 → ∃ y' ∈ U, f y y' ≠ 0)
    (hdim : ∀ y ∈ U, ∀ y' ∈ U, ∃ y'' ∈ U, y'' ≠ 0 ∧ f y y'' = 0 ∧ f y' y'' = 0) :
    ∃ z ∈ U, z ≠ 0 ∧ f z z = 0 := by
  obtain ⟨y₁, hy₁U, hy₁0, -, -⟩ := hdim 0 U.zero_mem 0 U.zero_mem
  by_cases h1 : f y₁ y₁ = 0
  · exact ⟨y₁, hy₁U, hy₁0, h1⟩
  set U' := U ⊓ LinearMap.ker (f.flip y₁) with hU'
  have hmem : ∀ y, y ∈ U' ↔ y ∈ U ∧ f y y₁ = 0 := fun y => by
    rw [hU', Submodule.mem_inf, LinearMap.mem_ker]
    exact Iff.rfl
  have hnd' : ∀ y ∈ U', y ≠ 0 → ∃ y' ∈ U', f y y' ≠ 0 := by
    intro y hy hy0
    obtain ⟨y', hy'U, hy'⟩ := hnd y ((hmem y).1 hy).1 hy0
    refine ⟨y' - (f y' y₁ * (f y₁ y₁)⁻¹) • y₁, (hmem _).2 ⟨U.sub_mem hy'U (U.smul_mem _ hy₁U),
      ?_⟩, ?_⟩
    · rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, mul_assoc,
        inv_mul_cancel₀ h1, mul_one, sub_self]
    · rwa [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, ((hmem y).1 hy).2,
        mul_zero, sub_zero]
  have hdim' : ∀ y ∈ U', ∃ y' ∈ U', y' ≠ 0 ∧ f y y' = 0 := by
    intro y hy
    obtain ⟨y'', hU, h0, h1', h2'⟩ := hdim y ((hmem y).1 hy).1 y₁ hy₁U
    exact ⟨y'', (hmem _).2 ⟨hU, by rw [hf.symm]; exact h2'⟩, h0, h1'⟩
  obtain ⟨y₂, hy₂, h2⟩ := exists_mem_norm_eq hf hnd' hdim' (c := -f y₁ y₁) (neg_ne_zero.2 h1)
  have h12 : f y₁ y₂ = 0 := by rw [hf.symm]; exact ((hmem y₂).1 hy₂).2
  refine ⟨y₁ + y₂, U.add_mem hy₁U ((hmem y₂).1 hy₂).1, fun h => h1 ?_, ?_⟩
  · have := congrArg (fun x => f x y₁) h
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.zero_left] at this
    rw [hf.symm y₂ y₁, h12, add_zero] at this
    exact this
  · rw [norm_add hf, h12, h2]
    ring

theorem mem_perpSub_one {a x : Fin m → ZMod 3} : x ∈ perpSub f ![a] ↔ f x a = 0 := by
  simp [mem_perpSub]

theorem mem_perpSub_two {a b x : Fin m → ZMod 3} :
    x ∈ perpSub f ![a, b] ↔ f x a = 0 ∧ f x b = 0 := by
  simp [mem_perpSub, Fin.forall_fin_succ]

theorem mem_perpSub_three {a b c x : Fin m → ZMod 3} :
    x ∈ perpSub f ![a, b, c] ↔ f x a = 0 ∧ f x b = 0 ∧ f x c = 0 := by
  simp [mem_perpSub, Fin.forall_fin_succ]

theorem nondegOn_perp_one (hf : IsF3Form f) {v : Fin m → ZMod 3} (hv : f v v = 1) :
    ∀ y ∈ perpSub f ![v], y ≠ 0 → ∃ y' ∈ perpSub f ![v], f y y' ≠ 0 := by
  refine nondegOn_of_proj hf (fun y => y - f y v • v) (fun y => mem_perpSub_one.2 ?_)
    fun x hx y => ?_
  · rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, mul_one, sub_self]
  · rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, mem_perpSub_one.1 hx,
      mul_zero, sub_zero]

theorem nondegOn_perp_two (hf : IsF3Form f) {u v : Fin m → ZMod 3} (hu : f u u = 1)
    (hv : f v v = 1) (huv : f u v = 0) :
    ∀ y ∈ perpSub f ![u, v], y ≠ 0 → ∃ y' ∈ perpSub f ![u, v], f y y' ≠ 0 := by
  have hvu : f v u = 0 := by rw [hf.symm]; exact huv
  refine nondegOn_of_proj hf (fun y => y - f y u • u - f y v • v)
    (fun y => mem_perpSub_two.2 ⟨?_, ?_⟩) fun x hx y => ?_
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hu, hvu]
    ring
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, huv]
    ring
  · obtain ⟨h1, h2⟩ := mem_perpSub_two.1 hx
    simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, h1, h2]
    ring

theorem nondegOn_perp_neg_one (hf : IsF3Form f) {x : Fin m → ZMod 3} (hx : f x x = -1) :
    ∀ y ∈ perpSub f ![x], y ≠ 0 → ∃ y' ∈ perpSub f ![x], f y y' ≠ 0 := by
  refine nondegOn_of_proj hf (fun y => y + f y x • x) (fun y => mem_perpSub_one.2 ?_)
    fun a ha y => ?_
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hx]
    ring
  · rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, mem_perpSub_one.1 ha,
      mul_zero, add_zero]

theorem nondegOn_perp_hyp (hf : IsF3Form f) {v z y : Fin m → ZMod 3} (hv : f v v = 1)
    (hzz : f z z = 0) (hzv : f z v = 0) (hyy : f y y = 0) (hyz : f y z = 1) (hyv : f y v = 0) :
    (∀ a, a - f a v • v - f a y • z - f a z • y ∈ perpSub f ![v, z, y]) ∧
      ∀ x ∈ perpSub f ![v, z, y], ∀ a, f x (a - f a v • v - f a y • z - f a z • y) = f x a := by
  have hvz : f v z = 0 := by rw [hf.symm]; exact hzv
  have hvy : f v y = 0 := by rw [hf.symm]; exact hyv
  have hzy : f z y = 1 := by rw [hf.symm]; exact hyz
  refine ⟨fun a => mem_perpSub_three.2 ⟨?_, ?_, ?_⟩, fun x hx a => ?_⟩
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, hzv, hyv]
    ring
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hvz, hzz, hyz]
    ring
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hvy, hzy, hyy]
    ring
  · obtain ⟨h1, h2, h3⟩ := mem_perpSub_three.1 hx
    simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, h1, h2, h3]
    ring

theorem exists_norm_eq (hf : IsF3Form f) (hm : 2 ≤ m) {c : ZMod 3} (hc : c ≠ 0) :
    ∃ v, f v v = c := by
  obtain ⟨v, -, hv⟩ := exists_mem_norm_eq hf (U := ⊤) (fun y _ hy0 => by
      by_contra! h
      exact hy0 (hf.nondeg y fun y' => h y' trivial))
    (fun y _ => by
      obtain ⟨y', h0, h⟩ := exists_ne_zero_perp (f := f) (k := 1) (by omega) ![y]
      exact ⟨y', trivial, h0, by rw [hf.symm]; simpa using h 0⟩) hc
  exact ⟨v, hv⟩

theorem exists_norm_eq_perp (hf : IsF3Form f) (hm : 3 ≤ m) {v : Fin m → ZMod 3}
    (hv : f v v = 1) {c : ZMod 3} (hc : c ≠ 0) : ∃ w, f w w = c ∧ f w v = 0 := by
  obtain ⟨w, hw, hwc⟩ := exists_mem_norm_eq hf (nondegOn_perp_one hf hv)
    (perpSub_twoDim hf (k := 1) (by omega) _) hc
  exact ⟨w, hwc, mem_perpSub_one.1 hw⟩

theorem exists_isotropic_perp (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3}
    (hv : f v v = 1) : ∃ z, z ≠ 0 ∧ f z z = 0 ∧ f z v = 0 := by
  obtain ⟨z, hz, hz0, hzz⟩ := exists_mem_isotropic hf (nondegOn_perp_one hf hv)
    (perpSub_threeDim hf (k := 1) (by omega) _)
  exact ⟨z, hz0, hzz, mem_perpSub_one.1 hz⟩

theorem exists_norm_eq_perp_two (hf : IsF3Form f) (hm : 4 ≤ m) {u v : Fin m → ZMod 3}
    (hu : f u u = 1) (hv : f v v = 1) (huv : f u v = 0) {c : ZMod 3} (hc : c ≠ 0) :
    ∃ y, f y y = c ∧ f y u = 0 ∧ f y v = 0 := by
  obtain ⟨y, hy, hyc⟩ := exists_mem_norm_eq hf (nondegOn_perp_two hf hu hv huv)
    (perpSub_twoDim hf (k := 2) (by omega) _) hc
  exact ⟨y, hyc, mem_perpSub_two.1 hy⟩

theorem exists_norm_one_ne_zero_ne_zero (hf : IsF3Form f) (hm : 4 ≤ m) {u v : Fin m → ZMod 3}
    (hu : f u u = 1) (hv : f v v = 1) (huv : f u v = 0) :
    ∃ x, f x x = 1 ∧ f x u ≠ 0 ∧ f x v ≠ 0 := by
  obtain ⟨y, hyy, hyu, hyv⟩ :=
    exists_norm_eq_perp_two hf hm hu hv huv (c := -1) (by decide)
  have hvu : f v u = 0 := by rw [hf.symm]; exact huv
  have huy : f u y = 0 := by rw [hf.symm]; exact hyu
  have hvy : f v y = 0 := by rw [hf.symm]; exact hyv
  refine ⟨u + v + y, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hu, hv, huv, hvu,
      huy, hvy, hyu, hyv, hyy]
    ring
  · simp only [LinearMap.BilinForm.add_left, hu, hvu, hyu]
    decide
  · simp only [LinearMap.BilinForm.add_left, hv, huv, hyv]
    decide

theorem exists_isotropic_perp_two (hf : IsF3Form f) (hm : 5 ≤ m) {u v : Fin m → ZMod 3}
    (hu : f u u = 1) (hv : f v v = 1) (huv : f u v = 0) :
    ∃ z, z ≠ 0 ∧ f z z = 0 ∧ f z u = 0 ∧ f z v = 0 := by
  obtain ⟨z, hz, hz0, hzz⟩ := exists_mem_isotropic hf (nondegOn_perp_two hf hu hv huv)
    (perpSub_threeDim hf (k := 2) (by omega) _)
  exact ⟨z, hz0, hzz, mem_perpSub_two.1 hz⟩

theorem eq_zero_of_forall_norm_one (hf : IsF3Form f) (hm : 3 ≤ m) {x : Fin m → ZMod 3}
    (h : ∀ y, f y y = 1 → f x y = 0) : x = 0 := by
  by_contra hx0
  have hcases : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = -1 := by decide
  rcases hcases (f x x) with h0 | h1 | h2
  · obtain ⟨y, hy⟩ : ∃ y, f x y ≠ 0 := by
      by_contra! h'
      exact hx0 (hf.nondeg x h')
    obtain ⟨t, ht⟩ := exists_norm_add_smul_eq hf (x := y) h0 (by rwa [hf.symm]) 1
    apply hy
    have := h _ ht
    rwa [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, h0, mul_zero,
      add_zero] at this
  · exact one_ne_zero (h1 ▸ h x h1)
  · obtain ⟨u, hu, huc⟩ := exists_mem_norm_eq hf (nondegOn_perp_neg_one hf h2)
      (perpSub_twoDim hf (k := 1) (by omega) _) (c := -1) (by decide)
    have hux : f u x = 0 := mem_perpSub_one.1 hu
    have hxu : f x u = 0 := by rw [hf.symm]; exact hux
    have := h (x + u) (by rw [norm_add hf, h2, hxu, huc]; decide)
    rw [LinearMap.BilinForm.add_right, h2, hxu] at this
    exact absurd this (by decide)

theorem exists_hyp_partner (hf : IsF3Form f) {v z : Fin m → ZMod 3} (hv : f v v = 1)
    (hz0 : z ≠ 0) (hzz : f z z = 0) (hzv : f z v = 0) :
    ∃ y, f y y = 0 ∧ f y z = 1 ∧ f y v = 0 := by
  obtain ⟨y₀, hy₀⟩ : ∃ y, f y z ≠ 0 := by
    by_contra! h
    exact hz0 (hf.nondeg z fun y => by rw [hf.symm]; exact h y)
  have hvz : f v z = 0 := by rw [hf.symm]; exact hzv
  set y₁ := y₀ - f y₀ v • v
  have h1z : f y₁ z = f y₀ z := by
    rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hvz, mul_zero, sub_zero]
  have h1v : f y₁ v = 0 := by
    rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, mul_one, sub_self]
  obtain ⟨y₂, h2z, h2v⟩ : ∃ y₂, f y₂ z = 1 ∧ f y₂ v = 0 :=
    ⟨(f y₁ z)⁻¹ • y₁, by rw [LinearMap.BilinForm.smul_left, inv_mul_cancel₀ (h1z ▸ hy₀)],
      by rw [LinearMap.BilinForm.smul_left, h1v, mul_zero]⟩
  refine ⟨y₂ + f y₂ y₂ • z, ?_, ?_, ?_⟩
  · rw [norm_add_smul hf, h2z, hzz]
    linear_combination f y₂ y₂ * three_eq_zero
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, h2z, hzz, mul_zero,
      add_zero]
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, h2v, hzv, mul_zero,
      add_zero]

theorem exists_norm_one_perp_isotropic (hf : IsF3Form f) (hm : 5 ≤ m) {v z : Fin m → ZMod 3}
    (hv : f v v = 1) (hz0 : z ≠ 0) (hzz : f z z = 0) (hzv : f z v = 0) :
    ∃ w, f w w = 1 ∧ f w v = 0 ∧ f w z = 0 := by
  obtain ⟨y, hyy, hyz, hyv⟩ := exists_hyp_partner hf hv hz0 hzz hzv
  obtain ⟨hpU, hp⟩ := nondegOn_perp_hyp hf hv hzz hzv hyy hyz hyv
  obtain ⟨w, hw, hww⟩ := exists_mem_norm_eq hf (nondegOn_of_proj hf _ hpU hp)
    (perpSub_twoDim hf (k := 3) (by omega) _) (c := 1) one_ne_zero
  obtain ⟨h1, h2, -⟩ := mem_perpSub_three.1 hw
  exact ⟨w, hww, h1, h2⟩

theorem exists_smul_eq_of_perp (hf : IsF3Form f) (hm : 5 ≤ m) {v z s : Fin m → ZMod 3}
    (hv : f v v = 1) (hz0 : z ≠ 0) (hzz : f z z = 0) (hzv : f z v = 0) (hsv : f s v = 0)
    (hs : ∀ w, f w w = 1 → f w v = 0 → f w z = 0 → f s w = 0) (hss : f s s = 0 ∨ f s s = 1) :
    ∃ γ : ZMod 3, s = γ • z := by
  obtain ⟨w₀, hw₀, hw₀v, hw₀z⟩ := exists_norm_one_perp_isotropic hf hm hv hz0 hzz hzv
  have hsz : f s z = 0 := by
    have h1 := hs w₀ hw₀ hw₀v hw₀z
    have h2 := hs (w₀ + z) (by rw [norm_add hf, hw₀, hw₀z, hzz]; ring)
      (by rw [LinearMap.BilinForm.add_left, hw₀v, hzv, add_zero])
      (by rw [LinearMap.BilinForm.add_left, hw₀z, hzz, add_zero])
    rwa [LinearMap.BilinForm.add_right, h1, zero_add] at h2
  rcases hss with hss | hss
  swap
  · exact absurd (hs s hss hsv hsz) (by rw [hss]; exact one_ne_zero)
  obtain ⟨y, hyy, hyz, hyv⟩ := exists_hyp_partner hf hv hz0 hzz hzv
  obtain ⟨hpU, hp⟩ := nondegOn_perp_hyp hf hv hzz hzv hyy hyz hyv
  refine ⟨f s y, ?_⟩
  by_contra hne
  have hzy : f z y = 1 := by rw [hf.symm]; exact hyz
  have hsU : s - f s y • z ∈ perpSub f ![v, z, y] := by
    refine mem_perpSub_three.2 ⟨?_, ?_, ?_⟩
    · rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hsv, hzv]; ring
    · rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hsz, hzz]; ring
    · rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hzy]; ring
  obtain ⟨x, hx, hsUx⟩ := nondegOn_of_proj hf _ hpU hp _ hsU (sub_ne_zero.2 hne)
  obtain ⟨hxv, hxz, -⟩ := mem_perpSub_three.1 hx
  have hsx : f s x ≠ 0 := by
    have hzx : f z x = 0 := by rw [hf.symm]; exact hxz
    rwa [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hzx, mul_zero,
      sub_zero] at hsUx
  obtain ⟨μ, hμ⟩ := exists_norm_add_smul_eq hf (x := x) hss (by rwa [hf.symm]) 1
  have := hs (x + μ • s) hμ
    (by rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxv, hsv]; ring)
    (by rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxz, hsz]; ring)
  rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hss, mul_zero,
    add_zero] at this
  exact hsx this

theorem exists_isotropic_pairings (hf : IsF3Form f) {v z₀ z : Fin m → ZMod 3} (hv : f v v = 1)
    (hz₀ : z₀ ≠ 0) (hz₀z₀ : f z₀ z₀ = 0) (hz₀v : f z₀ v = 0) (hzv : f z v = 0)
    (hz₀z : f z₀ z = 0) (hind : ∀ a : ZMod 3, z ≠ a • z₀) (c : ZMod 3) :
    ∃ x, f x x = 0 ∧ f x v = 0 ∧ f x z₀ = 1 ∧ f x z = c := by
  have hli : LinearIndependent (ZMod 3) ![v, z₀, z] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hg
    have h0 : g 0 = 0 := by
      have := congrArg (fun x => f x v) hg
      simpa [hv, hz₀v, hzv] using this
    rw [h0, zero_smul, zero_add] at hg
    have h2 : g 2 = 0 := by
      by_contra h2
      apply hind (-((g 2)⁻¹ * g 1))
      calc z = (g 2)⁻¹ • (g 2 • z) := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
        _ = (g 2)⁻¹ • -(g 1 • z₀) := by rw [eq_neg_of_add_eq_zero_right hg]
        _ = (-((g 2)⁻¹ * g 1)) • z₀ := by rw [smul_neg, smul_smul, neg_smul]
    have h1 : g 1 = 0 := by
      rw [h2, zero_smul, add_zero] at hg
      exact (smul_eq_zero.1 hg).resolve_right hz₀
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  obtain ⟨x, hx⟩ := exists_pairings hf hli ![0, 1, c]
  have hxv : f x v = 0 := by simpa using hx 0
  have hxz₀ : f x z₀ = 1 := by simpa using hx 1
  have hxz : f x z = c := by simpa using hx 2
  obtain ⟨t, ht⟩ := exists_norm_add_smul_eq hf (x := x) hz₀z₀ (by rw [hxz₀]; exact one_ne_zero) 0
  refine ⟨x + t • z₀, ht, ?_, ?_, ?_⟩
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxv, hz₀v]; ring
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxz₀, hz₀z₀]; ring
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxz, hz₀z]; ring

theorem exists_isotropic_pairings₄ (hf : IsF3Form f) {v z₀ z z' : Fin m → ZMod 3}
    (hv : f v v = 1) (hz₀ : z₀ ≠ 0) (hz₀z₀ : f z₀ z₀ = 0) (hz₀v : f z₀ v = 0) (hzz : f z z = 0)
    (hzv : f z v = 0) (hz'z' : f z' z' = 0) (hz'v : f z' v = 0) (hz₀z : f z₀ z = 0)
    (hz₀z' : f z₀ z' = 0) (hzz' : f z z' ≠ 0) :
    ∃ x, f x x = 0 ∧ f x v = 0 ∧ f x z₀ = 1 ∧ f x z = 1 ∧ f x z' = 1 := by
  have hvz : f v z = 0 := by rw [hf.symm]; exact hzv
  have hvz' : f v z' = 0 := by rw [hf.symm]; exact hz'v
  have hz'z : f z' z ≠ 0 := by rwa [hf.symm]
  have hli : LinearIndependent (ZMod 3) ![v, z₀, z, z'] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at hg
    have h0 : g 0 = 0 := by
      have := congrArg (fun x => f x v) hg
      simpa [hv, hz₀v, hzv, hz'v] using this
    have h3 : g 3 = 0 := by
      have := congrArg (fun x => f x z) hg
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hvz, hz₀z, hzz,
        LinearMap.BilinForm.zero_left] at this
      simpa [hz'z] using this
    have h2 : g 2 = 0 := by
      have := congrArg (fun x => f x z') hg
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hvz', hz₀z', hz'z',
        LinearMap.BilinForm.zero_left] at this
      simpa [hzz'] using this
    have h1 : g 1 = 0 := by
      rw [h0, h2, h3, zero_smul, zero_smul, zero_smul, zero_add, add_zero, add_zero] at hg
      exact (smul_eq_zero.1 hg).resolve_right hz₀
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  obtain ⟨x, hx⟩ := exists_pairings hf hli ![0, 1, 1, 1]
  have hxv : f x v = 0 := by simpa using hx 0
  have hxz₀ : f x z₀ = 1 := by simpa using hx 1
  have hxz : f x z = 1 := by simpa using hx 2
  have hxz' : f x z' = 1 := by simpa using hx 3
  obtain ⟨t, ht⟩ := exists_norm_add_smul_eq hf (x := x) hz₀z₀ (by rw [hxz₀]; exact one_ne_zero) 0
  refine ⟨x + t • z₀, ht, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxv, hz₀v]; ring
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxz₀, hz₀z₀]; ring
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxz, hz₀z]; ring
  · rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hxz', hz₀z']; ring

theorem exists_common_neighbor (hf : IsF3Form f) {v z₀ z y₁ y₂ : Fin m → ZMod 3}
    (hv : f v v = 1) (hz₀ : z₀ ≠ 0) (hz₀z₀ : f z₀ z₀ = 0) (hz₀v : f z₀ v = 0) (hzz : f z z = 0)
    (hzv : f z v = 0) (hz₀z : f z₀ z = 0) (hind : ∀ a : ZMod 3, z ≠ a • z₀)
    (h₁ : f y₁ z₀ ≠ 0) (h₁' : f y₁ z ≠ 0) (h₂ : f y₂ z₀ ≠ 0) (h₂' : f y₂ z ≠ 0)
    (hs : f y₁ z * f y₁ z₀ = f y₂ z * f y₂ z₀) :
    ∃ y, f y y = 0 ∧ f y v = 0 ∧ f y z₀ ≠ 0 ∧ f y z ≠ 0 ∧ f y y₁ ≠ 0 ∧ f y y₂ ≠ 0 ∧
      f y z * f y z₀ = -(f y₁ z * f y₁ z₀) := by
  set s := f y₁ z * f y₁ z₀ with hsdef
  obtain ⟨x₀, hx₀x₀, hx₀v, hx₀z₀, hx₀z⟩ :=
    exists_isotropic_pairings hf hv hz₀ hz₀z₀ hz₀v hzv hz₀z hind (-s)
  have hzz₀ : f z z₀ = 0 := by rw [hf.symm]; exact hz₀z
  have hkey : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → b * a * a + b ≠ 0 := by decide
  have hk : ∀ y : Fin m → ZMod 3, f y z₀ ≠ 0 → f y z ≠ 0 → f y z * f y z₀ = s →
      f (s • z₀ + z) y ≠ 0 := by
    intro y ha hb hy
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hf.symm z₀, hf.symm z, ← hy]
    exact hkey _ _ ha hb
  have hc : ∀ p₁ q₁ p₂ q₂ : ZMod 3, q₁ ≠ 0 → q₂ ≠ 0 → ∃ c, p₁ + c * q₁ ≠ 0 ∧ p₂ + c * q₂ ≠ 0 := by
    decide
  obtain ⟨c, hc₁, hc₂⟩ := hc (f x₀ y₁) (f (s • z₀ + z) y₁) (f x₀ y₂) (f (s • z₀ + z) y₂)
    (hk y₁ h₁ h₁' rfl) (hk y₂ h₂ h₂' hs.symm)
  have hs0 : s ≠ 0 := mul_ne_zero h₁' h₁
  refine ⟨x₀ + c • (s • z₀ + z), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hx₀x₀, hx₀z₀, hx₀z,
      hz₀z₀, hz₀z, hzz₀, hzz, hf.symm z₀ x₀, hf.symm z x₀]
    ring
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hx₀v, hz₀v, hzv]
    ring
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hx₀z₀, hz₀z₀, hzz₀]
    ring_nf
    exact one_ne_zero
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hx₀z, hz₀z, hzz]
    ring_nf
    exact neg_ne_zero.2 hs0
  · rwa [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
  · rwa [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hx₀z₀, hz₀z₀, hzz₀,
      hx₀z, hz₀z, hzz]
    ring

end F3

end CFSG.Fischer.Classification

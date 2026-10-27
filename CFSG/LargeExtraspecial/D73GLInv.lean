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
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
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

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.D73

open Matrix

section Block

variable {K V m : Type*} [CommRing K] [AddCommGroup V] [Module K V] [Fintype m] [DecidableEq m]

@[expose] noncomputable def blockEnd (s : (m → K) →ₗ[K] V) (π : V →ₗ[K] m → K) (Y : Matrix m m K) :
    V →ₗ[K] V :=
  LinearMap.id + s ∘ₗ (Y - 1).mulVecLin ∘ₗ π

theorem blockEnd_apply (s : (m → K) →ₗ[K] V) (π : V →ₗ[K] m → K) (Y : Matrix m m K) (v : V) :
    blockEnd s π Y v = v + s ((Y - 1) *ᵥ π v) := rfl

variable {s : (m → K) →ₗ[K] V} {π : V →ₗ[K] m → K}

theorem blockEnd_one_apply (v : V) : blockEnd s π 1 v = v := by
  simp [blockEnd_apply]

theorem blockEnd_blockEnd (hsπ : ∀ w, π (s w) = w) (Y Z : Matrix m m K) (v : V) :
    blockEnd s π Y (blockEnd s π Z v) = blockEnd s π (Y * Z) v := by
  rw [blockEnd_apply, blockEnd_apply, blockEnd_apply, map_add, hsπ, add_assoc, ← map_add]
  congr 2
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, sub_mul, one_mul]
  abel

@[expose] noncomputable def blockEquiv (hsπ : ∀ w, π (s w) = w) (σ : (Matrix m m K)ˣ) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (blockEnd s π σ) (blockEnd s π ↑σ⁻¹)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, blockEnd_blockEnd hsπ, Units.mul_inv, blockEnd_one_apply]; rfl)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, blockEnd_blockEnd hsπ, Units.inv_mul, blockEnd_one_apply]; rfl)

theorem blockEquiv_apply (hsπ : ∀ w, π (s w) = w) (σ : (Matrix m m K)ˣ) (v : V) :
    blockEquiv hsπ σ v = blockEnd s π σ v := rfl

theorem blockEquiv_symm_apply (hsπ : ∀ w, π (s w) = w) (σ : (Matrix m m K)ˣ) (v : V) :
    (blockEquiv hsπ σ).symm v = blockEnd s π ↑σ⁻¹ v := rfl

theorem mul_conj_apply (hsπ : ∀ w, π (s w) = w) {u : V ≃ₗ[K] V} {U : Matrix m m K}
    (hπu : ∀ v, π (u v) = U *ᵥ π v) (hus : ∀ w, u (s w) = s (U *ᵥ w))
    (huu : ∀ v, u (u v) = v) (hU : U * U = 1) (σ : (Matrix m m K)ˣ) (v : V) :
    (u * (blockEquiv hsπ σ * u * (blockEquiv hsπ σ)⁻¹)) v =
      blockEnd s π (U * Units.val σ * U * Units.val σ⁻¹) v := by
  have key : U * Units.val σ * U * Units.val σ⁻¹ - 1 = U * U * (Units.val σ⁻¹ - 1) +
      U * (Units.val σ - 1) * (U + U * (Units.val σ⁻¹ - 1)) := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_add, ← mul_assoc, hU]
    abel
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, blockEquiv_symm_apply, blockEquiv_apply,
    blockEnd_apply, map_add, hus, hπu, hsπ, huu]
  rw [add_assoc, ← map_add]
  congr 2
  rw [key]
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, map_add]
  abel

theorem blockEnd_pow_apply (hsπ : ∀ w, π (s w) = w) {x : V ≃ₗ[K] V} {X : Matrix m m K}
    (hx : ∀ v, x v = blockEnd s π X v) (n : ℕ) (v : V) : (x ^ n) v = blockEnd s π (X ^ n) v := by
  induction n generalizing v with
  | zero => rw [pow_zero, pow_zero, blockEnd_one_apply]; rfl
  | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hx, blockEnd_blockEnd hsπ, ← pow_succ']

theorem orderOf_eq_four_of_apply (hsπ : ∀ w, π (s w) = w) {x : V ≃ₗ[K] V} {X : Matrix m m K}
    (hx : ∀ v, x v = blockEnd s π X v) (h4 : X ^ 4 = 1) (h2 : X ^ 2 ≠ 1) : orderOf x = 4 := by
  refine orderOf_eq_prime_pow (p := 2) (n := 1) (fun h => h2 ?_) ?_
  · have hw : ∀ w, (X ^ 2 - 1) *ᵥ w = 0 := fun w => by
      have h1 := blockEnd_pow_apply hsπ hx 2 (s w)
      rw [show (2 : ℕ) = 2 ^ 1 from rfl, h, blockEnd_apply, hsπ] at h1
      have h3 : s ((X ^ 2 ^ 1 - 1) *ᵥ w) = 0 := by
        have h1' : s w + s ((X ^ 2 ^ 1 - 1) *ᵥ w) = s w + 0 := by rw [add_zero]; exact h1.symm
        exact add_left_cancel h1'
      simpa [hsπ] using congrArg π h3
    rw [← sub_eq_zero]
    exact Matrix.ext_of_mulVec_single fun i => by rw [hw, Matrix.zero_mulVec]
  · refine LinearEquiv.ext fun v => ?_
    rw [blockEnd_pow_apply hsπ hx, show 2 ^ (1 + 1) = 4 from rfl, h4, blockEnd_one_apply]
    rfl

end Block

section Dual

variable {K V m : Type*} [CommRing K] [AddCommGroup V] [Module K V] [Fintype m] [DecidableEq m]

theorem pi_linearCombination {e : m → V} {φ : m → V →ₗ[K] K}
    (h : ∀ i j, φ i (e j) = (1 : Matrix m m K) i j) (w : m → K) :
    LinearMap.pi φ (Fintype.linearCombination K e w) = w := by
  ext i
  simp [Fintype.linearCombination_apply, h, Matrix.one_apply]

omit [DecidableEq m] in
theorem pi_apply_eq_mulVec {φ : m → V →ₗ[K] K} {u : V →ₗ[K] V} {U : Matrix m m K}
    (h : ∀ i v, φ i (u v) = ∑ j, U i j * φ j v) (v : V) :
    LinearMap.pi φ (u v) = U *ᵥ LinearMap.pi φ v := by
  ext i
  simp [h, Matrix.mulVec, dotProduct]

omit [DecidableEq m] in
theorem apply_linearCombination {e : m → V} {u : V →ₗ[K] V} {U : Matrix m m K}
    (h : ∀ j, u (e j) = ∑ i, U i j • e i) (w : m → K) :
    u (Fintype.linearCombination K e w) = Fintype.linearCombination K e (U *ᵥ w) := by
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, h, Finset.smul_sum, smul_smul,
    Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

theorem exists_orderOf_eq_four_of_dual {u : V ≃ₗ[K] V} (huu : ∀ v, u (u v) = v) (e : m → V)
    (φ : m → V →ₗ[K] K) (U : Matrix m m K) (hU : U * U = 1)
    (hφe : ∀ i j, φ i (e j) = (1 : Matrix m m K) i j)
    (hφu : ∀ i v, φ i (u v) = ∑ j, U i j * φ j v) (hue : ∀ j, u (e j) = ∑ i, U i j • e i)
    (σ : (Matrix m m K)ˣ) (h4 : (U * Units.val σ * U * Units.val σ⁻¹) ^ 4 = 1)
    (h2 : (U * Units.val σ * U * Units.val σ⁻¹) ^ 2 ≠ 1) :
    ∃ g : V ≃ₗ[K] V, orderOf (u * (g * u * g⁻¹)) = 4 := by
  have hsπ := pi_linearCombination hφe
  exact ⟨blockEquiv hsπ σ, orderOf_eq_four_of_apply hsπ
    (mul_conj_apply hsπ (pi_apply_eq_mulVec (u := u.toLinearMap) hφu)
      (apply_linearCombination (u := u.toLinearMap) hue) huu hU σ) h4 h2⟩

end Dual

section Two

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero_zmod_two (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem eq_one_of_ne_zero_zmod_two {t : ZMod 2} (h : t ≠ 0) : t = 1 := by
  revert t; decide

theorem exists_form_eq_one {p : Submodule (ZMod 2) V} {x : V} (hx : x ∉ p) :
    ∃ f : V →ₗ[ZMod 2] ZMod 2, f x = 1 ∧ ∀ y ∈ p, f y = 0 := by
  obtain ⟨f, hf, hp⟩ := Submodule.exists_le_ker_of_notMem hx
  exact ⟨f, eq_one_of_ne_zero_zmod_two hf, fun y hy => hp hy⟩

theorem exists_orderOf_eq_four_case_one {u : V ≃ₗ[ZMod 2] V} (huu : ∀ v, u (u v) = v)
    {N : V →ₗ[ZMod 2] V} (huN : ∀ v, u v = v + N v) (hNN : ∀ v, N (N v) = 0) {a c : V}
    (ha : N a ≠ 0) (hc : N c = 0) (hcR : c ∉ LinearMap.range N) :
    ∃ g : V ≃ₗ[ZMod 2] V, orderOf (u * (g * u * g⁻¹)) = 4 := by
  obtain ⟨α₀, hα₀, -⟩ := exists_form_eq_one (p := ⊥) (x := N a) (by simpa using ha)
  obtain ⟨γ₀, hγ₀, hγ₀N⟩ := exists_form_eq_one hcR
  have hγ₀N' : ∀ v, γ₀ (N v) = 0 := fun v => hγ₀N _ (LinearMap.mem_range_self N v)
  set β : V →ₗ[ZMod 2] ZMod 2 := α₀ ∘ₗ N with hβdef
  have hβ : ∀ v, β v = α₀ (N v) := fun v => rfl
  set γ : V →ₗ[ZMod 2] ZMod 2 := γ₀ + γ₀ a • β with hγdef
  have hγ : ∀ v, γ v = γ₀ v + γ₀ a * β v := fun v => rfl
  set α : V →ₗ[ZMod 2] ZMod 2 := α₀ + α₀ a • β + α₀ c • γ with hαdef
  have hα : ∀ v, α v = α₀ v + α₀ a * β v + α₀ c * γ v := fun v => rfl
  have hβN : ∀ v, β (N v) = 0 := fun v => by rw [hβ, hNN, map_zero]
  have hγN : ∀ v, γ (N v) = 0 := fun v => by rw [hγ, hγ₀N', hβN, mul_zero, add_zero]
  have hαN : ∀ v, α (N v) = β v := fun v => by
    rw [hα, hβN, hγN, mul_zero, mul_zero, add_zero, add_zero, hβ]
  have hNb : N (N a) = 0 := hNN a
  refine exists_orderOf_eq_four_of_dual huu ![a, N a, c] ![β, α, γ]
    !![1, 0, 0; 1, 1, 0; 0, 0, 1] (by decide) ?_ ?_ ?_
    ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩
    (by decide) (by decide)
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hα, hβ, hγ, hα₀, hγ₀, hNb, hc, hγ₀N', CharTwo.add_self_eq_zero]
  · intro i v
    fin_cases i <;> simp [Fin.sum_univ_three, huN, hβN, hαN, hγN, add_comm]
  · intro j
    fin_cases j <;> simp [Fin.sum_univ_three, huN, hNb, hc]

theorem exists_orderOf_eq_four_case_two {u : V ≃ₗ[ZMod 2] V} (huu : ∀ v, u (u v) = v)
    {N : V →ₗ[ZMod 2] V} (huN : ∀ v, u v = v + N v) (hNN : ∀ v, N (N v) = 0) {a₁ a₂ : V}
    (h₁ : N a₁ ∉ Submodule.span (ZMod 2) {N a₂}) (h₂ : N a₂ ∉ Submodule.span (ZMod 2) {N a₁}) :
    ∃ g : V ≃ₗ[ZMod 2] V, orderOf (u * (g * u * g⁻¹)) = 4 := by
  obtain ⟨α₁, hα₁, hα₁'⟩ := exists_form_eq_one h₁
  obtain ⟨α₂, hα₂, hα₂'⟩ := exists_form_eq_one h₂
  have hα₁₂ : α₁ (N a₂) = 0 := hα₁' _ (Submodule.mem_span_singleton_self _)
  have hα₂₁ : α₂ (N a₁) = 0 := hα₂' _ (Submodule.mem_span_singleton_self _)
  set β₁ : V →ₗ[ZMod 2] ZMod 2 := α₁ ∘ₗ N with hβ₁def
  set β₂ : V →ₗ[ZMod 2] ZMod 2 := α₂ ∘ₗ N with hβ₂def
  have hβ₁ : ∀ v, β₁ v = α₁ (N v) := fun v => rfl
  have hβ₂ : ∀ v, β₂ v = α₂ (N v) := fun v => rfl
  set γ₁ : V →ₗ[ZMod 2] ZMod 2 := α₁ + α₁ a₁ • β₁ + α₁ a₂ • β₂ with hγ₁def
  set γ₂ : V →ₗ[ZMod 2] ZMod 2 := α₂ + α₂ a₁ • β₁ + α₂ a₂ • β₂ with hγ₂def
  have hγ₁ : ∀ v, γ₁ v = α₁ v + α₁ a₁ * β₁ v + α₁ a₂ * β₂ v := fun v => rfl
  have hγ₂ : ∀ v, γ₂ v = α₂ v + α₂ a₁ * β₁ v + α₂ a₂ * β₂ v := fun v => rfl
  have hβ₁N : ∀ v, β₁ (N v) = 0 := fun v => by rw [hβ₁, hNN, map_zero]
  have hβ₂N : ∀ v, β₂ (N v) = 0 := fun v => by rw [hβ₂, hNN, map_zero]
  have hγ₁N : ∀ v, γ₁ (N v) = β₁ v := fun v => by
    rw [hγ₁, hβ₁N, hβ₂N, mul_zero, mul_zero, add_zero, add_zero, hβ₁]
  have hγ₂N : ∀ v, γ₂ (N v) = β₂ v := fun v => by
    rw [hγ₂, hβ₁N, hβ₂N, mul_zero, mul_zero, add_zero, add_zero, hβ₂]
  have hN₁ : N (N a₁) = 0 := hNN a₁
  have hN₂ : N (N a₂) = 0 := hNN a₂
  refine exists_orderOf_eq_four_of_dual huu ![a₁, N a₁, a₂, N a₂] ![β₁, γ₁, β₂, γ₂]
    !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, 1] (by decide) ?_ ?_ ?_
    ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1],
      !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1], by decide, by decide⟩
    (by decide) (by decide)
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hγ₁, hγ₂, hβ₁, hβ₂, hα₁, hα₂, hα₁₂, hα₂₁, hN₁, hN₂, CharTwo.add_self_eq_zero]
  · intro i v
    fin_cases i <;> simp [Fin.sum_univ_four, huN, hβ₁N, hβ₂N, hγ₁N, hγ₂N, add_comm]
  · intro j
    fin_cases j <;> simp [Fin.sum_univ_four, huN, hN₁, hN₂]

theorem exists_orderOf_mul_conj_eq_four_of_le_finrank [FiniteDimensional (ZMod 2) V]
    (hV : 3 ≤ finrank (ZMod 2) V) {u : V ≃ₗ[ZMod 2] V} (hu : orderOf u = 2) :
    ∃ g : V ≃ₗ[ZMod 2] V, orderOf (u * (g * u * g⁻¹)) = 4 := by
  have huu : ∀ v, u (u v) = v := fun v => by
    have h := pow_orderOf_eq_one u
    rw [hu, pow_two] at h
    rw [← LinearEquiv.mul_apply, h]
    rfl
  have hu1 : u ≠ 1 := fun h => by
    rw [h, orderOf_one] at hu
    exact absurd hu (by decide)
  set N : V →ₗ[ZMod 2] V := u.toLinearMap - LinearMap.id with hNdef
  have hNv : ∀ v, N v = u v - v := fun v => rfl
  have huN : ∀ v, u v = v + N v := fun v => by rw [hNv]; abel
  have hNN : ∀ v, N (N v) = 0 := fun v => by
    rw [hNv, hNv, map_sub, huu]
    rw [show v - u v - (u v - v) = (v + v) - (u v + u v) by abel, add_self_eq_zero_zmod_two,
      add_self_eq_zero_zmod_two, sub_zero]
  obtain ⟨a, ha⟩ : ∃ a, N a ≠ 0 := by
    by_contra h
    push Not at h
    exact hu1 (LinearEquiv.ext fun v => by
      have h' := h v
      rw [hNv, sub_eq_zero] at h'
      exact h')
  by_cases hc : ∃ c, N c = 0 ∧ c ∉ LinearMap.range N
  · obtain ⟨c, hc0, hcR⟩ := hc
    exact exists_orderOf_eq_four_case_one huu huN hNN ha hc0 hcR
  · push Not at hc
    have hker : LinearMap.ker N ≤ LinearMap.range N := fun c hc0 => hc c hc0
    have hrank := LinearMap.finrank_range_add_finrank_ker N
    have hle := Submodule.finrank_mono hker
    have h2 : 2 ≤ finrank (ZMod 2) (LinearMap.range N) := by omega
    have hnle : ¬ LinearMap.range N ≤ Submodule.span (ZMod 2) {N a} := fun h => by
      have := Submodule.finrank_mono h
      rw [finrank_span_singleton ha] at this
      omega
    obtain ⟨_, ⟨a₂, rfl⟩, h₂⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    refine exists_orderOf_eq_four_case_two huu huN hNN (a₁ := a) (a₂ := a₂) ?_ h₂
    intro h₁
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h₁
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) t with rfl | rfl
    · rw [zero_smul] at ht
      exact ha ht.symm
    · rw [one_smul] at ht
      exact h₂ (ht ▸ Submodule.mem_span_singleton_self _)

end Two

theorem exists_orderOf_mul_conj_eq_four {k : ℕ} (hk : 3 ≤ k) {u : GL (Fin k) (ZMod 2)}
    (hu : orderOf u = 2) : ∃ g : GL (Fin k) (ZMod 2), orderOf (u * (g * u * g⁻¹)) = 4 := by
  set e : GL (Fin k) (ZMod 2) ≃* ((Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin k → ZMod 2))
  obtain ⟨g, hg⟩ := exists_orderOf_mul_conj_eq_four_of_le_finrank
    (by rw [Module.finrank_fin_fun]; exact hk) (u := e u) (by rw [MulEquiv.orderOf_eq, hu])
  refine ⟨e.symm g, ?_⟩
  rw [← MulEquiv.orderOf_eq e, map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hg

end CFSG.LargeExtraspecial.DW.D73

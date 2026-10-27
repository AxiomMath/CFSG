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

namespace CFSG.QuasithinUnique.A5.Kc3Irr

variable {F : Type*} [Field F] [CharP F 2]

@[expose] def pactF (σ : Equiv.Perm (Fin 5)) : (Fin 5 → F) →ₗ[F] (Fin 5 → F) :=
  LinearMap.funLeft F F ((σ⁻¹ : Equiv.Perm (Fin 5)) : Fin 5 → Fin 5)

omit [CharP F 2] in
theorem pactF_apply (σ : Equiv.Perm (Fin 5)) (x : Fin 5 → F) (i : Fin 5) :
    pactF σ x i = x (σ⁻¹ i) := rfl

omit [CharP F 2] in
theorem pactF_mul (σ τ : Equiv.Perm (Fin 5)) (x : Fin 5 → F) :
    pactF (σ * τ) x = pactF σ (pactF τ x) := by
  funext i
  simp [pactF_apply, mul_inv_rev]

@[expose] def sumF : (Fin 5 → F) →ₗ[F] F := ∑ i, LinearMap.proj i

omit [CharP F 2] in
theorem sumF_apply (x : Fin 5 → F) : sumF x = ∑ i, x i := by
  simp [sumF, LinearMap.sum_apply]

@[expose] def delta5 : Submodule F (Fin 5 → F) := LinearMap.ker sumF

omit [CharP F 2] in
theorem mem_delta5 {x : Fin 5 → F} : x ∈ (delta5 : Submodule F (Fin 5 → F)) ↔ ∑ i, x i = 0 := by
  rw [delta5, LinearMap.mem_ker, sumF_apply]

omit [CharP F 2] in
theorem pactF_mem_delta5 (σ : Equiv.Perm (Fin 5)) {x : Fin 5 → F}
    (hx : x ∈ (delta5 : Submodule F (Fin 5 → F))) :
    pactF σ x ∈ (delta5 : Submodule F (Fin 5 → F)) := by
  rw [mem_delta5] at hx ⊢
  simp only [pactF_apply]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact hx

omit [CharP F 2] in
theorem finrank_delta5 : Module.finrank F (delta5 : Submodule F (Fin 5 → F)) = 4 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (sumF : (Fin 5 → F) →ₗ[F] F)
  have h2 : LinearMap.range (sumF : (Fin 5 → F) →ₗ[F] F) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    rw [sumF_apply, Finset.sum_eq_single (0 : Fin 5)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  change Module.finrank F (LinearMap.ker (sumF : (Fin 5 → F) →ₗ[F] F)) = 4
  omega

theorem two_trans : ∀ i j : Fin 5, i ≠ j → ∃ ρ : Equiv.Perm (Fin 5),
    Equiv.Perm.sign ρ = 1 ∧ ρ i = 0 ∧ ρ j = 1 := by
  decide +kernel

@[expose] def σ₀ : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def τ₀ : Equiv.Perm (Fin 5) := Equiv.swap 1 4 * Equiv.swap 2 3

theorem sign_σ₀ : Equiv.Perm.sign σ₀ = 1 := by decide +kernel

theorem sign_τ₀ : Equiv.Perm.sign τ₀ = 1 := by decide +kernel

theorem σ₀_inv : (σ₀⁻¹ 0 = 1) ∧ (σ₀⁻¹ 1 = 0) ∧ (σ₀⁻¹ 2 = 3) ∧ (σ₀⁻¹ 3 = 2) ∧ (σ₀⁻¹ 4 = 4) := by
  decide +kernel

theorem τ₀_inv : (τ₀⁻¹ 0 = 0) ∧ (τ₀⁻¹ 1 = 4) ∧ (τ₀⁻¹ 2 = 3) ∧ (τ₀⁻¹ 3 = 2) ∧ (τ₀⁻¹ 4 = 1) := by
  decide +kernel

@[expose] def gen (i : Fin 5) : Fin 5 → F := Pi.single i 1 + Pi.single 4 1

omit [CharP F 2] in
theorem pactF_gen (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    pactF σ (gen i : Fin 5 → F) = Pi.single (σ i) 1 + Pi.single (σ 4) 1 := by
  funext j
  simp only [pactF_apply, gen, Pi.add_apply, Pi.single_apply]
  have h1 : σ⁻¹ j = i ↔ j = σ i := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  have h2 : σ⁻¹ j = 4 ↔ j = σ 4 := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  simp only [h1, h2]

theorem key_identity (x : Fin 5 → F) :
    pactF τ₀ (pactF σ₀ x + x) + (pactF σ₀ x + x) = (x 0 + x 1) • (gen 1 : Fin 5 → F) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨a0, a1, a2, a3, a4⟩ := σ₀_inv
  obtain ⟨b0, b1, b2, b3, b4⟩ := τ₀_inv
  funext a
  fin_cases a <;>
    simp [pactF_apply, gen, a0, a1, a2, a3, a4, b0, b1, b2, b3, b4] <;>
    first
    | linear_combination (x 0 + x 1) * h2
    | linear_combination (x 4) * h2
    | linear_combination (x 2 + x 3) * h2

theorem decomp {x : Fin 5 → F} (hx : x ∈ (delta5 : Submodule F (Fin 5 → F))) :
    x = ∑ i, x i • (gen i : Fin 5 → F) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [mem_delta5, Fin.sum_univ_five] at hx
  funext a
  fin_cases a <;> simp [gen, Fin.sum_univ_five, Pi.single_apply]
  linear_combination (-1 : F) * hx

theorem irr_delta5 {U : Submodule F (Fin 5 → F)} (hU : U ≤ delta5)
    (hinv : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → ∀ x ∈ U, pactF σ x ∈ U)
    (hne : U ≠ ⊥) : U = delta5 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxd : x ∈ (delta5 : Submodule F (Fin 5 → F)) := hU hxU
  have hpair : ∃ i j : Fin 5, i ≠ j ∧ x i ≠ x j := by
    by_contra hcon
    push Not at hcon
    have hconst : ∀ i, x i = x 0 := fun i => by
      by_cases h : i = 0
      · rw [h]
      · exact hcon i 0 h
    have hsum := (mem_delta5.1 hxd)
    rw [Fin.sum_univ_five, hconst 1, hconst 2, hconst 3, hconst 4] at hsum
    have h5 : x 0 = 0 := by linear_combination hsum - (2 * x 0) * h2
    apply hx0
    funext i
    rw [hconst i, h5]
    rfl
  obtain ⟨i, j, hij, hxij⟩ := hpair
  obtain ⟨ρ, hρs, hρi, hρj⟩ := two_trans i j hij
  set x' := pactF ρ x with hx'
  have hx'U : x' ∈ U := hinv ρ hρs x hxU
  have hx'01 : x' 0 ≠ x' 1 := by
    simp only [hx', pactF_apply]
    rw [← hρi, ← hρj]
    simpa using hxij
  have hy : pactF σ₀ x' + x' ∈ U := U.add_mem (hinv σ₀ sign_σ₀ x' hx'U) hx'U
  have hz : pactF τ₀ (pactF σ₀ x' + x') + (pactF σ₀ x' + x') ∈ U :=
    U.add_mem (hinv τ₀ sign_τ₀ _ hy) hy
  rw [key_identity] at hz
  have hd : x' 0 + x' 1 ≠ 0 := by
    intro h
    apply hx'01
    linear_combination h - (x' 1) * h2
  have hg1 : (gen 1 : Fin 5 → F) ∈ U := by
    have := U.smul_mem (x' 0 + x' 1)⁻¹ hz
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at this
  have hgi : ∀ i : Fin 5, (gen i : Fin 5 → F) ∈ U := by
    intro i
    by_cases hi : i = 4
    · have : (gen i : Fin 5 → F) = 0 := by
        subst hi
        funext a
        simp only [gen, Pi.add_apply, Pi.zero_apply]
        linear_combination ((Pi.single (4 : Fin 5) (1 : F) : Fin 5 → F) a) * h2
      rw [this]
      exact U.zero_mem
    · obtain ⟨ρ1, hρ1s, hρ1i, hρ14⟩ := two_trans i 4 hi
      obtain ⟨ρ2, hρ2s, hρ21, hρ24⟩ := two_trans 1 4 (by decide)
      have hρ : (ρ1⁻¹ * ρ2) 1 = i ∧ (ρ1⁻¹ * ρ2) 4 = 4 := by
        constructor
        · simp only [Equiv.Perm.mul_apply, hρ21]
          rw [← hρ1i]
          simp
        · simp only [Equiv.Perm.mul_apply, hρ24]
          rw [← hρ14]
          simp
      have hs : Equiv.Perm.sign (ρ1⁻¹ * ρ2) = 1 := by
        rw [map_mul, map_inv, hρ1s, hρ2s]
        simp
      have := hinv _ hs _ hg1
      rw [pactF_gen, hρ.1, hρ.2] at this
      exact this
  refine le_antisymm hU fun y hy => ?_
  rw [decomp hy]
  exact U.sum_mem fun i _ => U.smul_mem _ (hgi i)

end CFSG.QuasithinUnique.A5.Kc3Irr

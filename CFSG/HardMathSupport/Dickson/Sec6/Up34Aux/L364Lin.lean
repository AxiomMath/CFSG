module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Projectivization.Independence
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
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

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Lin

open Polynomial

theorem perfect_hom_trivial {G A : Type*} [Group G] [CommGroup A] {D : Subgroup G}
    (hD : ⁅D, D⁆ = D) (f : G →* A) : ∀ d ∈ D, f d = 1 := by
  intro d hd
  have h : ⁅D, D⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    simp [commutatorElement_def, mul_comm]
  rw [hD] at h
  exact h hd


section Decomp

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem sub_mul_quad (T : Module.End K V) (μ : K) :
    (T - μ • (1 : Module.End K V)) * (T * T + μ • T + (μ ^ 2) • 1) =
      T * T * T - (μ ^ 3) • 1 := by
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc,
    smul_smul]
  module


theorem isCompl_ker_eigen (T : Module.End K V) (μ c : K) (hμ : μ ≠ 0) (h3 : (3 : K) ≠ 0)
    (hT3 : T * T * T = c • (1 : Module.End K V)) (hμ3 : μ ^ 3 = c) :
    IsCompl (LinearMap.ker (T - μ • (1 : Module.End K V)))
      (LinearMap.ker (T * T + μ • T + (μ ^ 2) • (1 : Module.End K V))) := by
  have hprod : (T - μ • (1 : Module.End K V)) * (T * T + μ • T + (μ ^ 2) • 1) = 0 := by
    rw [sub_mul_quad, hT3, ← hμ3, sub_self]
  have hcomm : (T * T + μ • T + (μ ^ 2) • (1 : Module.End K V)) * (T - μ • 1) =
      (T - μ • 1) * (T * T + μ • T + (μ ^ 2) • 1) := by
    simp only [sub_mul, mul_add, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_one, mul_assoc, smul_smul]
    module
  have hprod' : (T * T + μ • T + (μ ^ 2) • (1 : Module.End K V)) * (T - μ • 1) = 0 := by
    rw [hcomm, hprod]
  have hid : (T * T + μ • T + (μ ^ 2) • (1 : Module.End K V)) -
      (T + (2 * μ) • 1) * (T - μ • 1) = (3 * μ ^ 2) • 1 := by
    simp only [sub_mul, mul_add, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_one, mul_assoc, smul_smul]
    module
  have hc3 : (3 * μ ^ 2 : K) ≠ 0 := mul_ne_zero h3 (pow_ne_zero 2 hμ)
  have happly : ∀ x : V, (T * T + μ • T + (μ ^ 2) • (1 : Module.End K V)) x -
      (T + (2 * μ) • (1 : Module.End K V)) ((T - μ • 1) x) = (3 * μ ^ 2) • x := by
    intro x
    have := congrArg (fun f : Module.End K V => f x) hid
    simpa using this
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxe hxq
    rw [LinearMap.mem_ker] at hxe hxq
    have := happly x
    rw [hxe, hxq] at this
    simp only [map_zero, sub_zero] at this
    exact (smul_eq_zero.1 this.symm).resolve_left hc3
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (3 * μ ^ 2)⁻¹ • (T * T + μ • T + (μ ^ 2) • (1 : Module.End K V)) x +
        (-(3 * μ ^ 2)⁻¹) • ((T + (2 * μ) • (1 : Module.End K V)) ((T - μ • 1) x)) := by
      have h := happly x
      have h' : (T * T + μ • T + (μ ^ 2) • (1 : Module.End K V)) x =
          (3 * μ ^ 2) • x + (T + (2 * μ) • (1 : Module.End K V)) ((T - μ • 1) x) := by
        rw [← h]; abel
      rw [h', smul_add, smul_smul, inv_mul_cancel₀ hc3, one_smul, neg_smul, add_assoc,
        add_neg_cancel, add_zero]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [LinearMap.mem_ker, map_smul]
      have := congrArg (fun f : Module.End K V => f x) hprod
      simp only [Module.End.mul_apply, LinearMap.zero_apply] at this
      rw [this, smul_zero]
    · rw [LinearMap.mem_ker, map_smul]
      have hq : (T * T + μ • T + (μ ^ 2) • (1 : Module.End K V)) * (T + (2 * μ) • 1) *
          (T - μ • 1) = 0 := by
        have hc2 : (T * T + μ • T + (μ ^ 2) • (1 : Module.End K V)) * (T + (2 * μ) • 1) =
            (T + (2 * μ) • 1) * (T * T + μ • T + (μ ^ 2) • 1) := by
          simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
            mul_assoc, smul_smul]
          module
        rw [hc2, mul_assoc, hprod', mul_zero]
      have := congrArg (fun f : Module.End K V => f x) hq
      simp only [Module.End.mul_apply, LinearMap.zero_apply] at this
      rw [this, smul_zero]


theorem commutant_comm [Module.Finite K V] (hV : Module.finrank K V = 3) (T : Module.End K V)
    (c : K) (hT3 : T * T * T = c • (1 : Module.End K V)) (hroot : ∀ r : K, r ^ 3 ≠ c) :
    ∀ d₁ d₂ : Module.End K V, d₁ * T = T * d₁ → d₂ * T = T * d₂ → d₁ * d₂ = d₂ * d₁ := by
  classical
  set p₀ : K[X] := X ^ 3 - C c with hp₀
  have hnat : p₀.natDegree = 3 := natDegree_X_pow_sub_C
  have hirr : Irreducible p₀ := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by simp [hnat]) fun x hx => hroot x ?_
    simpa [hp₀, sub_eq_zero] using hx
  have hev : aeval T p₀ = 0 := by
    simp only [hp₀, map_sub, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    rw [pow_three', hT3, sub_self]
  haveI : Nontrivial V := Module.finrank_pos_iff.1 (by rw [hV]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hli : LinearIndependent K (fun i : Fin 3 => (T ^ (i : ℕ)) v) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set q : K[X] := ∑ i : Fin 3, C (g i) * X ^ (i : ℕ) with hq
    have hqv' : aeval T q v = ∑ i : Fin 3, g i • (T ^ (i : ℕ)) v := by
      simp [hq, map_sum, Algebra.algebraMap_eq_smul_one, LinearMap.sum_apply,
        LinearMap.smul_apply]
    have hqv : aeval T q v = 0 := by rw [hqv']; exact hg
    have hqdeg : q.degree < 3 := by
      have := degree_sum_fin_lt g
      simpa [hq] using this
    by_cases hq0 : q = 0
    · intro i
      have := congrArg (fun r => r.coeff (i : ℕ)) hq0
      simpa [hq, Polynomial.finset_sum_coeff, coeff_C_mul, coeff_X_pow, Fin.val_inj] using this
    · exfalso
      have hnd : ¬ p₀ ∣ q := by
        intro hd
        have := Polynomial.degree_le_of_dvd hd hq0
        rw [Polynomial.degree_eq_natDegree (hirr.ne_zero), hnat] at this
        have h3 : ((3 : ℕ) : WithBot ℕ) ≤ q.degree := by exact_mod_cast this
        exact absurd (lt_of_le_of_lt h3 hqdeg) (by simp)
      obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hirr).2 hnd
      have h1 : aeval T (a * p₀ + b * q) = 1 := by rw [hab, map_one]
      have h2 : v = (aeval T a) ((aeval T p₀) v) + (aeval T b) (aeval T q v) := by
        have := congrArg (fun f : Module.End K V => f v) h1
        simpa [map_add, map_mul, Module.End.mul_apply] using this.symm
      rw [hqv, hev] at h2
      simp at h2
      exact hv h2
  let b : Module.Basis (Fin 3) K V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV])
  have hb : ∀ i, b i = (T ^ (i : ℕ)) v := fun i => by simp [b]
  have hpoly : ∀ d : Module.End K V, d * T = T * d → ∃ q : K[X], d = aeval T q := by
    intro d hd
    have hdv : d v = ∑ i : Fin 3, (b.repr (d v) i) • (T ^ (i : ℕ)) v := by
      conv_lhs => rw [← b.sum_repr (d v)]
      simp [hb]
    refine ⟨∑ i : Fin 3, C (b.repr (d v) i) * X ^ (i : ℕ), ?_⟩
    refine b.ext fun i => ?_
    have hcomm : ∀ n : ℕ, d * T ^ n = T ^ n * d := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hd, ← mul_assoc]
    have hdT : d ((T ^ (i : ℕ)) v) = (T ^ (i : ℕ)) (d v) := by
      have := congrArg (fun f : Module.End K V => f v) (hcomm i)
      simpa [Module.End.mul_apply] using this
    have hRHS : (aeval T (∑ j : Fin 3, C (b.repr (d v) j) * X ^ (j : ℕ))) ((T ^ (i : ℕ)) v) =
        ∑ j : Fin 3, (b.repr (d v) j) • (T ^ (j : ℕ)) ((T ^ (i : ℕ)) v) := by
      simp [map_sum, Algebra.algebraMap_eq_smul_one, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [hb i, hdT, hRHS]
    conv_lhs => rw [hdv]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_add, ← pow_add, add_comm]
  intro d₁ d₂ h₁ h₂
  obtain ⟨q₁, rfl⟩ := hpoly d₁ h₁
  obtain ⟨q₂, rfl⟩ := hpoly d₂ h₂
  rw [← map_mul, ← map_mul, mul_comm]

end Decomp


section Fixed

open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K] [Finite K]

theorem exists_common_eigenvectors {M : Type*} [AddCommGroup M] [Module K M]
    (hM : Module.finrank K M = 2) (hK : Nat.card K % 3 = 1) {S : Type*} [Group S] [Finite S]
    (hS : IsPGroup 3 S) (ρ : S →* (M ≃ₗ[K] M)) :
    ∃ m₁ m₂ : M, LinearIndependent K ![m₁, m₂] ∧
      ∀ s : S, ∃ a₁ a₂ : Kˣ, ρ s m₁ = (a₁ : K) • m₁ ∧ ρ s m₂ = (a₂ : K) • m₂ := by
  classical
  haveI : Module.Finite K M := Module.finite_of_finrank_pos (by omega)
  haveI : Finite M := Module.finite_of_finite K
  letI : MulAction S (ℙ K M) := MulAction.compHom (ℙ K M) ρ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (ℙ K M) = Nat.card K + 1 := Projectivization.card_of_finrank_two K M hM
  have hmod := hS.card_modEq_card_fixedPoints (α := ℙ K M)
  have hfix : 1 < Nat.card (MulAction.fixedPoints S (ℙ K M)) := by
    by_contra h
    push Not at h
    have h1 : Nat.card (MulAction.fixedPoints S (ℙ K M)) = 0 ∨
        Nat.card (MulAction.fixedPoints S (ℙ K M)) = 1 := by omega
    rw [hcard] at hmod
    unfold Nat.ModEq at hmod
    rcases h1 with h1 | h1 <;> rw [h1] at hmod <;> omega
  haveI : Nontrivial (MulAction.fixedPoints S (ℙ K M)) := Finite.one_lt_card_iff_nontrivial.1 hfix
  obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, hne⟩ := exists_pair_ne (MulAction.fixedPoints S (ℙ K M))
  have hx12 : x₁ ≠ x₂ := fun h => hne (Subtype.ext h)
  refine ⟨x₁.rep, x₂.rep, ?_, fun s => ?_⟩
  · rw [← Projectivization.independent_pair_iff_ne] at hx12
    have hfun : (Projectivization.rep ∘ ![x₁, x₂] : Fin 2 → M) = ![x₁.rep, x₂.rep] := by
      funext i; fin_cases i <;> rfl
    rw [Projectivization.independent_iff] at hx12
    rwa [hfun] at hx12
  · have key : ∀ x : ℙ K M, ρ s • x = x → ∃ a : Kˣ, ρ s x.rep = (a : K) • x.rep := by
      intro x hx
      have h2 : Projectivization.mk K (ρ s • x.rep)
          ((smul_ne_zero_iff_ne (ρ s)).mpr x.rep_nonzero) =
          Projectivization.mk K x.rep x.rep_nonzero := by
        rw [← Projectivization.smul_mk (ρ s) x.rep_nonzero, Projectivization.mk_rep]
        exact hx
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).1 h2
      exact ⟨a, by simpa [Units.smul_def] using ha.symm⟩
    obtain ⟨a₁, h₁⟩ := key x₁ (hx₁ s)
    obtain ⟨a₂, h₂⟩ := key x₂ (hx₂ s)
    exact ⟨a₁, a₂, h₁, h₂⟩


theorem cyclic_of_eigen {M : Type*} [AddCommGroup M] [Module K M] (hM : Module.finrank K M = 2)
    {S : Type*} [Group S] (ρ : S →* (M ≃ₗ[K] M)) (hρ : Function.Injective ρ)
    (hdet : ∀ s, LinearEquiv.det (ρ s) = 1) {m₁ m₂ : M} (hli : LinearIndependent K ![m₁, m₂])
    (heig : ∀ s : S, ∃ a₁ a₂ : Kˣ, ρ s m₁ = (a₁ : K) • m₁ ∧ ρ s m₂ = (a₂ : K) • m₂) :
    IsCyclic S := by
  classical
  have hm₁ : m₁ ≠ 0 := by simpa using hli.ne_zero 0
  choose a₁ a₂ h₁ h₂ using heig
  have hcancel : ∀ a b : Kˣ, (a : K) • m₁ = (b : K) • m₁ → a = b := by
    intro a b h
    exact Units.ext (smul_left_injective K hm₁ h)
  let b : Module.Basis (Fin 2) K M :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hM])
  have hb0 : b 0 = m₁ := by simp [b]
  have hb1 : b 1 = m₂ := by simp [b]
  have e1 : ∀ s, ρ s (b 0) = (a₁ s : K) • b 0 := fun s => by rw [hb0]; exact h₁ s
  have e2 : ∀ s, ρ s (b 1) = (a₂ s : K) • b 1 := fun s => by rw [hb1]; exact h₂ s
  have hdet' : ∀ s, (a₁ s : K) * (a₂ s : K) = 1 := by
    intro s
    have h1 := hdet s
    have h2 : LinearMap.det ((ρ s : M ≃ₗ[K] M) : M →ₗ[K] M) = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) h1
      simpa [LinearEquiv.coe_det] using this
    rw [← LinearMap.det_toMatrix b] at h2
    have hmat : LinearMap.toMatrix b b ((ρ s : M ≃ₗ[K] M) : M →ₗ[K] M) =
        Matrix.diagonal ![(a₁ s : K), (a₂ s : K)] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [LinearMap.toMatrix_apply, e1, e2, Module.Basis.repr_self, Finsupp.single_apply,
          Matrix.diagonal_apply]
    rw [hmat, Matrix.det_diagonal, Fin.prod_univ_two] at h2
    simpa using h2
  let f : S →* Kˣ :=
    { toFun := a₁
      map_one' := by
        apply hcancel
        rw [← h₁ 1, map_one]
        simp
      map_mul' := fun s t => by
        apply hcancel
        have : ρ (s * t) m₁ = ρ s (ρ t m₁) := by rw [map_mul]; rfl
        rw [← h₁ (s * t), this, h₁ t, map_smul, h₁ s, smul_smul]
        simp [mul_comm] }
  haveI : IsCyclic Kˣ := inferInstance
  refine isCyclic_of_injective f ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker] at hs
  have ha1 : (a₁ s : K) = 1 := by
    have : a₁ s = 1 := hs
    simp [this]
  have ha2 : (a₂ s : K) = 1 := by
    have := hdet' s
    rwa [ha1, one_mul] at this
  have hsm : ρ s = ρ 1 := by
    refine LinearEquiv.toLinearMap_injective (b.ext fun i => ?_)
    fin_cases i
    · simp [e1, ha1]
    · simp [e2, ha2]
  rw [Subgroup.mem_bot]
  exact hρ hsm

end Fixed


section Perfect

variable {K : Type*} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]

theorem perfect_hom_trivial' {G A : Type*} [Group G] [CommGroup A] [hG : Group.IsPerfect G]
    (f : G →* A) (x : G) : f x = 1 := by
  have hx : x ∈ commutator G := by simp
  have h : commutator G ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    simp [commutatorElement_def, mul_comm]
  exact h hx

theorem perfect_fixes_line {D : Subgroup (Module.End K V)ˣ} (hD : ⁅D, D⁆ = D) {L : Submodule K V}
    (hL : Module.finrank K L = 1)
    (hLD : ∀ d ∈ D, ∀ x ∈ L, ((d : Module.End K V)) x ∈ L) :
    ∀ d ∈ D, ∀ x ∈ L, (d : Module.End K V) x = x := by
  haveI : Group.IsPerfect D := Subgroup.isPerfect_iff.2 hD
  obtain ⟨l, hl0, hl⟩ := finrank_eq_one_iff'.1 hL
  have hℓ0 : (l : V) ≠ 0 := fun h => hl0 (Subtype.ext h)
  have hex : ∀ d : D, ∃ a : Kˣ, ((d : (Module.End K V)ˣ) : Module.End K V) (l : V) =
      (a : K) • (l : V) := by
    intro d
    obtain ⟨c, hc⟩ := hl ⟨((d : (Module.End K V)ˣ) : Module.End K V) (l : V),
      hLD d d.2 l l.2⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      have h0 : ((d : (Module.End K V)ˣ) : Module.End K V) (l : V) = 0 := by
        simpa using (congrArg Subtype.val hc).symm
      have := congrArg (((d : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V) h0
      simp only [map_zero] at this
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel] at this
      exact hℓ0 (by simpa using this)
    exact ⟨Units.mk0 c hc0, by simpa using (congrArg Subtype.val hc).symm⟩
  choose a ha using hex
  have hcancel : ∀ x y : Kˣ, (x : K) • (l : V) = (y : K) • (l : V) → x = y := fun x y h =>
    Units.ext (smul_left_injective K hℓ0 h)
  let χ : D →* Kˣ :=
    { toFun := a
      map_one' := by
        apply hcancel
        rw [← ha 1]
        simp
      map_mul' := fun s t => by
        apply hcancel
        have h1 : ((((s * t : D) : (Module.End K V)ˣ)) : Module.End K V) (l : V) =
            ((s : (Module.End K V)ˣ) : Module.End K V)
              (((t : (Module.End K V)ˣ) : Module.End K V) (l : V)) := rfl
        rw [← ha (s * t), h1, ha t, map_smul, ha s, smul_smul]
        simp [mul_comm] }
  intro d hd x hx
  obtain ⟨c, hc⟩ := hl ⟨x, hx⟩
  have hx' : x = c • (l : V) := (congrArg Subtype.val hc).symm
  have hχ : a ⟨d, hd⟩ = 1 := perfect_hom_trivial' χ ⟨d, hd⟩
  rw [hx', map_smul, ha ⟨d, hd⟩, hχ]
  simp


theorem exists_omega (hK : Nat.card K % 3 = 1) :
    (3 : K) ≠ 0 ∧ ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ 1 + ω + ω ^ 2 = 0 := by
  constructor
  · intro h
    have hp : CharP K 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).2 (by exact_mod_cast h)
    haveI := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 3
    have : 3 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self 3 (by exact n.ne_zero)
    omega
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hdvd : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units]
      have : 0 < Nat.card K := Nat.card_pos
      omega
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    have h3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    have h1 : w ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hw
      omega
    have hw3 : (w : K) ^ 3 = 1 := by simpa using congrArg (fun u : Kˣ => (u : K)) h3
    refine ⟨(w : K), hw3, ?_, ?_⟩
    · intro h
      exact h1 (Units.ext h)
    · 
      have hw1 : (w : K) ≠ 1 := fun h => h1 (Units.ext h)
      have : ((w : K) - 1) * (1 + (w : K) + (w : K) ^ 2) = 0 := by linear_combination hw3
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hw1)

end Perfect


section Restrict

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] noncomputable def restrictHom (S : Subgroup (Module.End K V)ˣ) (M : Submodule K V)
    (hSM : ∀ s ∈ S, ∀ x ∈ M, ((s : Module.End K V)) x ∈ M) : S →* (M ≃ₗ[K] M) where
  toFun s := LinearEquiv.ofLinear
    (LinearMap.restrict (s.1 : Module.End K V) (hSM s.1 s.2))
    (LinearMap.restrict ((s.1⁻¹ : (Module.End K V)ˣ) : Module.End K V)
      (hSM s.1⁻¹ (S.inv_mem s.2)))
    (LinearMap.ext fun x => Subtype.ext (by
      simp only [LinearMap.comp_apply, LinearMap.restrict_coe_apply, LinearMap.id_apply]
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]; rfl))
    (LinearMap.ext fun x => Subtype.ext (by
      simp only [LinearMap.comp_apply, LinearMap.restrict_coe_apply, LinearMap.id_apply]
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]; rfl))
  map_one' := by
    ext x
    simp [LinearEquiv.ofLinear_apply]
  map_mul' := fun s t => by
    ext x
    simp [LinearEquiv.ofLinear_apply]

theorem restrictHom_apply (S : Subgroup (Module.End K V)ˣ) (M : Submodule K V)
    (hSM : ∀ s ∈ S, ∀ x ∈ M, ((s : Module.End K V)) x ∈ M) (s : S) (x : M) :
    ((restrictHom S M hSM s x : M) : V) = ((s : (Module.End K V)ˣ) : Module.End K V) x := rfl

end Restrict


section Reducible

variable {K : Type*} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module.Finite K V]

theorem det_eq_det_restrict {L M : Submodule K V} (hLM : IsCompl L M)
    (u : (Module.End K V)ˣ) (hL : ∀ x ∈ L, (u : Module.End K V) x = x)
    (hM : ∀ x ∈ M, (u : Module.End K V) x ∈ M) :
    LinearMap.det (u : Module.End K V) = LinearMap.det (LinearMap.restrict (u : Module.End K V) hM) := by
  let e : (L × M) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl L M hLM
  let f : L × M →ₗ[K] L × M :=
    LinearMap.prodMap LinearMap.id (LinearMap.restrict (u : Module.End K V) hM)
  have hef : (e : (L × M) →ₗ[K] V) ∘ₗ f = (u : Module.End K V) ∘ₗ (e : (L × M) →ₗ[K] V) :=
    LinearMap.ext fun p => by
      obtain ⟨l, m⟩ := p
      simp [e, f, hL l l.2]
  have hu : (u : Module.End K V) = (e : (L × M) →ₗ[K] V) ∘ₗ f ∘ₗ (e.symm : V →ₗ[K] (L × M)) :=
    LinearMap.ext fun x => by
      have := congrArg (fun g : (L × M) →ₗ[K] V => g (e.symm x)) hef
      simpa using this.symm
  calc LinearMap.det (u : Module.End K V)
      = LinearMap.det ((e : (L × M) →ₗ[K] V) ∘ₗ f ∘ₗ (e.symm : V →ₗ[K] (L × M))) :=
        congrArg LinearMap.det hu
    _ = LinearMap.det f := LinearMap.det_conj f e
    _ = LinearMap.det (LinearMap.restrict (u : Module.End K V) hM) := by
        rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]


theorem cyclic_of_reducible (hK : Nat.card K % 3 = 1) {L M : Submodule K V} (hLM : IsCompl L M)
    (hL : Module.finrank K L = 1) (hM : Module.finrank K M = 2)
    {D : Subgroup (Module.End K V)ˣ} (hD : ⁅D, D⁆ = D)
    (hLD : ∀ d ∈ D, ∀ x ∈ L, (d : Module.End K V) x ∈ L)
    (hMD : ∀ d ∈ D, ∀ x ∈ M, (d : Module.End K V) x ∈ M)
    (S : Subgroup (Module.End K V)ˣ) [Finite S] (hSD : S ≤ D) (hS : IsPGroup 3 S) :
    IsCyclic S := by
  have hfix := perfect_fixes_line hD hL hLD
  have hSM : ∀ s ∈ S, ∀ x ∈ M, (s : Module.End K V) x ∈ M := fun s hs x hx => hMD s (hSD hs) x hx
  let ρ := restrictHom S M hSM
  have hdetD : ∀ d ∈ D, LinearMap.det (d : Module.End K V) = 1 := by
    intro d hd
    haveI : Group.IsPerfect D := Subgroup.isPerfect_iff.2 hD
    have := perfect_hom_trivial' ((Units.map (LinearMap.det : Module.End K V →* K)).comp D.subtype)
      ⟨d, hd⟩
    simpa using congrArg (fun u : Kˣ => (u : K)) this
  have hdet : ∀ s : S, LinearEquiv.det (ρ s) = 1 := by
    intro s
    apply Units.ext
    rw [LinearEquiv.coe_det]
    have h1 := det_eq_det_restrict hLM (s : (Module.End K V)ˣ) (hfix s (hSD s.2))
      (hSM s s.2)
    rw [Units.val_one, ← hdetD s (hSD s.2), h1]
    rfl
  have hρ : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    obtain ⟨l, hl, m, hm, rfl⟩ : ∃ l ∈ L, ∃ m ∈ M, l + m = x := by
      have : x ∈ L ⊔ M := by rw [hLM.sup_eq_top]; trivial
      exact Submodule.mem_sup.1 this
    have hm' : (s : (Module.End K V)ˣ).val m = m := by
      have := congrArg (fun e : M ≃ₗ[K] M => (e ⟨m, hm⟩ : V)) hs
      rw [← restrictHom_apply S M hSM s ⟨m, hm⟩]
      simpa using this
    simp [map_add, hfix s (hSD s.2) l hl, hm']
  obtain ⟨m₁, m₂, hli, heig⟩ := exists_common_eigenvectors hM hK hS ρ
  exact cyclic_of_eigen hM ρ hρ hdet hli heig

end Reducible


section Main

variable {K : Type*} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module.Finite K V]

theorem exists_eigenvalue (hK : Nat.card K % 3 = 1) (hV : Module.finrank K V = 3)
    (T : Module.End K V) (c r : K) (hT3 : T * T * T = c • (1 : Module.End K V)) (hr : r ^ 3 = c) :
    ∃ μ : K, μ ^ 3 = c ∧ ∃ v : V, v ≠ 0 ∧ T v = μ • v := by
  obtain ⟨-, ω, hω3, -, hω⟩ := exists_omega hK
  haveI : Nontrivial V := Module.finrank_pos_iff.1 (by rw [hV]; norm_num)
  have h1 : (1 : K[X]) + C ω + C ω ^ 2 = 0 := by
    have := congrArg C hω
    simpa using this
  have h2 : C ω ^ 3 - 1 = (0 : K[X]) := by
    have := congrArg C hω3
    simp only [map_pow, map_one] at this
    rw [this, sub_self]
  obtain ⟨a, ha⟩ : ∃ a : K, a = ω * r := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : K, b = ω ^ 2 * r := ⟨_, rfl⟩
  have hpoly : (X - C r) * (X - C a) * (X - C b) = X ^ 3 - C c := by
    rw [← hr, ha, hb]
    simp only [map_mul, map_pow]
    linear_combination (-(C r) * X ^ 2 + C r ^ 2 * X) * h1 + (C r ^ 2 * X - C r ^ 3) * h2
  have hT0 : (T - r • (1 : Module.End K V)) * (T - a • 1) * (T - b • 1) = 0 := by
    have := congrArg (aeval T) hpoly
    simp only [map_mul, map_sub, aeval_X, aeval_C, map_pow, Algebra.algebraMap_eq_smul_one] at this
    rw [this, pow_three', hT3, sub_self]
  by_contra hno
  push Not at hno
  have key : ∀ x : K, x ^ 3 = c → Function.Injective ⇑(T - x • (1 : Module.End K V)) := by
    intro x hx
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    by_contra hv0
    exact hno x hx v hv0 (by simpa [sub_eq_zero] using hv)
  have e1 := key r hr
  have e2 := key a (by rw [ha, mul_pow, hω3, one_mul, hr])
  have e3 := key b (by rw [hb, mul_pow, ← pow_mul, mul_comm 2 3, pow_mul, hω3, one_pow, one_mul, hr])
  have hinj : Function.Injective ⇑((T - r • (1 : Module.End K V)) * (T - a • 1) * (T - b • 1)) :=
    (e1.comp e2).comp e3
  rw [hT0] at hinj
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (hinj (by simp))


theorem three_subgroup_cyclic (hK : Nat.card K % 3 = 1) (hV : Module.finrank K V = 3)
    (T : Module.End K V) (c : K) (hc : c ≠ 0) (hT3 : T * T * T = c • (1 : Module.End K V))
    (hT : ∀ a : K, T ≠ a • (1 : Module.End K V))
    {D : Subgroup (Module.End K V)ˣ} (hD : ⁅D, D⁆ = D)
    (hDT : ∀ d ∈ D, (d : Module.End K V) * T = T * d)
    (S : Subgroup (Module.End K V)ˣ) [Finite S] (hSD : S ≤ D) (hS : IsPGroup 3 S) :
    IsCyclic S := by
  by_cases hroot : ∃ r : K, r ^ 3 = c
  · obtain ⟨r, hr⟩ := hroot
    obtain ⟨μ, hμ3, v, hv, hTv⟩ := exists_eigenvalue hK hV T c r hT3 hr
    have hμ : μ ≠ 0 := by
      rintro rfl
      apply hc
      rw [← hμ3]
      norm_num
    obtain ⟨h3, -⟩ := exists_omega hK
    have hcompl := isCompl_ker_eigen T μ c hμ h3 hT3 hμ3
    set E := LinearMap.ker (T - μ • (1 : Module.End K V)) with hE
    set W := LinearMap.ker (T * T + μ • T + (μ ^ 2) • (1 : Module.End K V)) with hW
    have hEinv : ∀ d ∈ D, ∀ x ∈ E, (d : Module.End K V) x ∈ E := by
      intro d hd x hx
      rw [hE, LinearMap.mem_ker] at hx ⊢
      have hc' : (d : Module.End K V) * (T - μ • 1) = (T - μ • 1) * d := by
        rw [mul_sub, sub_mul, hDT d hd, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
      have := congrArg (fun f : Module.End K V => f x) hc'
      simp only [Module.End.mul_apply] at this
      rw [← this, hx, map_zero]
    have hWinv : ∀ d ∈ D, ∀ x ∈ W, (d : Module.End K V) x ∈ W := by
      intro d hd x hx
      rw [hW, LinearMap.mem_ker] at hx ⊢
      have hdT := hDT d hd
      have hdTT : (d : Module.End K V) * (T * T) = (T * T) * d := by
        calc (d : Module.End K V) * (T * T) = ((d : Module.End K V) * T) * T := (mul_assoc _ _ _).symm
          _ = (T * (d : Module.End K V)) * T := by rw [hdT]
          _ = T * ((d : Module.End K V) * T) := mul_assoc _ _ _
          _ = T * (T * d) := by rw [hdT]
          _ = (T * T) * d := (mul_assoc _ _ _).symm
      have hc' : (d : Module.End K V) * (T * T + μ • T + (μ ^ 2) • 1) =
          (T * T + μ • T + (μ ^ 2) • 1) * d := by
        rw [mul_add, mul_add, add_mul, add_mul, hdTT, mul_smul_comm, smul_mul_assoc, hdT,
          mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
      have := congrArg (fun f : Module.End K V => f x) hc'
      simp only [Module.End.mul_apply] at this
      rw [← this, hx, map_zero]
    have hvE : v ∈ E := by
      rw [hE, LinearMap.mem_ker, LinearMap.sub_apply, hTv]
      simp
    have hEbot : E ≠ ⊥ := fun h => hv (by simpa [h] using hvE)
    have hEtop : E ≠ ⊤ := by
      intro h
      apply hT μ
      ext x
      have : x ∈ E := by rw [h]; trivial
      rw [hE, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
      simpa using this
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    have hE1 : 1 ≤ Module.finrank K E := Submodule.one_le_finrank_iff.2 hEbot
    have hE2 : Module.finrank K E < Module.finrank K V :=
      Submodule.finrank_lt hEtop
    rcases (show Module.finrank K E = 1 ∨ Module.finrank K E = 2 by omega) with h | h
    · exact cyclic_of_reducible hK hcompl h (by omega) hD hEinv hWinv S hSD hS
    · exact cyclic_of_reducible hK hcompl.symm (by omega) h hD hWinv hEinv S hSD hS
  · have hcomm := commutant_comm hV T c hT3 (fun r hr => hroot ⟨r, hr⟩)
    have hDbot : D = ⊥ := by
      refine le_antisymm ?_ bot_le
      calc D = ⁅D, D⁆ := hD.symm
        _ ≤ ⊥ := by
          rw [Subgroup.commutator_le]
          intro a ha b hb
          rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
          exact Units.ext (hcomm a b (hDT a ha) (hDT b hb))
    haveI : Subsingleton S := ⟨fun a b => by
      have ha : (a : (Module.End K V)ˣ) ∈ (⊥ : Subgroup _) := hDbot ▸ hSD a.2
      have hb : (b : (Module.End K V)ˣ) ∈ (⊥ : Subgroup _) := hDbot ▸ hSD b.2
      exact Subtype.ext ((Subgroup.mem_bot.1 ha).trans (Subgroup.mem_bot.1 hb).symm)⟩
    exact isCyclic_of_subsingleton

end Main

end CFSG.HardMathSupport.Dickson.Sec6.Up34Lin

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

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix
open scoped commutatorElement

section PlaneBasic

variable {K : Type} [Field K]

@[expose] def planeNrm (a : K) (p : Fin 2 → K) : K := p 0 ^ 2 + p 0 * p 1 + a * p 1 ^ 2

@[expose] def nrm2 (a α β : K) : K := α ^ 2 + α * β + a * β ^ 2

@[expose] def rotM (a α β : K) : Matrix (Fin 2) (Fin 2) K := !![α, a * β; β, α + β]

theorem rotM_mulVec (a α β : K) (p : Fin 2 → K) :
    rotM a α β *ᵥ p = ![α * p 0 + a * β * p 1, β * p 0 + (α + β) * p 1] := by
  ext i
  fin_cases i <;> simp [rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem rotM_mul (a α β α' β' : K) :
    rotM a α β * rotM a α' β' = rotM a (α * α' + a * β * β') (α * β' + β * α' + β * β') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rotM_one_zero (a : K) : rotM a 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM]

theorem nrm2_one_zero (a : K) : nrm2 a 1 0 = 1 := by simp [nrm2]

end PlaneBasic

section Plane

variable {K : Type} [Field K] [CharP K 2]

theorem planeNrm_rot (a α β : K) (p : Fin 2 → K) :
    planeNrm a (rotM a α β *ᵥ p) = nrm2 a α β * planeNrm a p := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [rotM_mulVec]
  simp only [planeNrm, nrm2, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (2 * a * α * β * p 0 * p 1 + a * α * β * p 1 ^ 2 + a * β ^ 2 * p 0 * p 1 +
    a * β ^ 2 * p 1 ^ 2) * h2

theorem nrm2_mul (a α β α' β' : K) :
    nrm2 a (α * α' + a * β * β') (α * β' + β * α' + β * β') = nrm2 a α β * nrm2 a α' β' := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [nrm2]
  linear_combination (2 * a * α * α' * β * β' + a * α * β * β' ^ 2 + a * α' * β ^ 2 * β' +
    a * β ^ 2 * β' ^ 2) * h2

theorem rotM_mul_inv (a α β : K) (h : nrm2 a α β = 1) :
    rotM a α β * rotM a (α + β) β = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [rotM_mul, ← rotM_one_zero a]
  have h' : α ^ 2 + α * β + a * β ^ 2 = 1 := h
  have e1 : α * (α + β) + a * β * β = 1 := by
    linear_combination h'
  have e2 : α * β + β * (α + β) + β * β = 0 := by
    linear_combination (α * β + β ^ 2) * h2
  rw [e1, e2]

theorem rotM_inv_mul (a α β : K) (h : nrm2 a α β = 1) :
    rotM a (α + β) β * rotM a α β = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [rotM_mul, ← rotM_one_zero a]
  have h' : α ^ 2 + α * β + a * β ^ 2 = 1 := h
  have e1 : (α + β) * α + a * β * β = 1 := by
    linear_combination h'
  have e2 : (α + β) * β + β * α + β * β = 0 := by
    linear_combination (α * β + β ^ 2) * h2
  rw [e1, e2]

theorem nrm2_inv (a α β : K) (h : nrm2 a α β = 1) : nrm2 a (α + β) β = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h' : α ^ 2 + α * β + a * β ^ 2 = 1 := h
  show (α + β) ^ 2 + (α + β) * β + a * β ^ 2 = 1
  linear_combination h' + (α * β + β ^ 2) * h2

@[expose] def rotGL (a α β : K) (h : nrm2 a α β = 1) : GL (Fin 2) K :=
  ⟨rotM a α β, rotM a (α + β) β, rotM_mul_inv a α β h, rotM_inv_mul a α β h⟩

theorem rotGL_val (a α β : K) (h : nrm2 a α β = 1) :
    (rotGL a α β h : Matrix (Fin 2) (Fin 2) K) = rotM a α β := rfl

@[expose] def Tgrp (a : K) : Subgroup (GL (Fin 2) K) where
  carrier := {g | ∃ α β, nrm2 a α β = 1 ∧ (g : Matrix (Fin 2) (Fin 2) K) = rotM a α β}
  one_mem' := ⟨1, 0, nrm2_one_zero a, by rw [rotM_one_zero]; rfl⟩
  mul_mem' := by
    rintro _ _ ⟨α, β, hn, hg⟩ ⟨α', β', hn', hg'⟩
    refine ⟨α * α' + a * β * β', α * β' + β * α' + β * β', ?_, ?_⟩
    · rw [nrm2_mul, hn, hn', mul_one]
    · rw [Units.val_mul, hg, hg', rotM_mul]
  inv_mem' := by
    rintro g ⟨α, β, hn, hg⟩
    refine ⟨α + β, β, nrm2_inv a α β hn, ?_⟩
    have h1 : (g : Matrix (Fin 2) (Fin 2) K) * rotM a (α + β) β = 1 := by
      rw [hg]
      exact rotM_mul_inv a α β hn
    calc ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          ((g : Matrix (Fin 2) (Fin 2) K) * rotM a (α + β) β) := by rw [h1, Matrix.mul_one]
      _ = rotM a (α + β) β := by rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem mem_Tgrp_iff (a : K) (g : GL (Fin 2) K) :
    g ∈ Tgrp a ↔ ∃ α β, nrm2 a α β = 1 ∧ (g : Matrix (Fin 2) (Fin 2) K) = rotM a α β := Iff.rfl

theorem sq_injective_K : ∀ x y : K, x ^ 2 = y ^ 2 → x = y := by
  intro x y h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact h
  · rw [CharTwo.neg_eq] at h
    exact h

theorem exists_sq_K [Finite K] (x : K) : ∃ y : K, y ^ 2 = x := by
  obtain ⟨y, hy⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) x
  exact ⟨y, by rw [hy, sq]⟩

theorem card_nrm2_one [Finite K] (a : K) (ha : ∀ z : K, z ^ 2 + z + a ≠ 0) :
    Nat.card {p : K × K // nrm2 a p.1 p.2 = 1} = Nat.card K + 1 := by
  classical
  have hne : ∀ t : K, t ^ 2 + t + a ≠ 0 := ha
  let β : K → K := fun t => Classical.choose (exists_sq_K ((t ^ 2 + t + a)⁻¹))
  have hβ : ∀ t, β t ^ 2 = (t ^ 2 + t + a)⁻¹ := fun t =>
    Classical.choose_spec (exists_sq_K ((t ^ 2 + t + a)⁻¹))
  have hβ0 : ∀ t, β t ≠ 0 := by
    intro t h0
    have h1 := hβ t
    rw [h0] at h1
    have h2 : (t ^ 2 + t + a)⁻¹ = 0 := by rw [← h1]; norm_num
    exact hne t (inv_eq_zero.1 h2)
  have hmem : ∀ t, nrm2 a (t * β t) (β t) = 1 := by
    intro t
    have h1 : (t ^ 2 + t + a) * β t ^ 2 = 1 := by
      rw [hβ t, mul_inv_cancel₀ (hne t)]
    simp only [nrm2]
    linear_combination h1
  let f : Option K → {p : K × K // nrm2 a p.1 p.2 = 1} := fun o =>
    match o with
    | none => ⟨(1, 0), nrm2_one_zero a⟩
    | some t => ⟨(t * β t, β t), hmem t⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro (_ | t) (_ | t') h
      · rfl
      · exfalso
        have := congrArg (fun p : {p : K × K // nrm2 a p.1 p.2 = 1} => p.1.2) h
        exact hβ0 t' this.symm
      · exfalso
        have := congrArg (fun p : {p : K × K // nrm2 a p.1 p.2 = 1} => p.1.2) h
        exact hβ0 t this
      · have h2 := congrArg (fun p : {p : K × K // nrm2 a p.1 p.2 = 1} => p.1.2) h
        have h1 := congrArg (fun p : {p : K × K // nrm2 a p.1 p.2 = 1} => p.1.1) h
        simp only [f] at h1 h2
        have : t = t' := by
          rw [h2] at h1
          exact mul_right_cancel₀ (hβ0 t') h1
        rw [this]
    · rintro ⟨⟨α, γ⟩, hp⟩
      by_cases hγ : γ = 0
      · subst hγ
        have h1 : α ^ 2 = 1 ^ 2 := by simpa [nrm2] using hp
        have := sq_injective_K _ _ h1
        subst this
        exact ⟨none, rfl⟩
      · refine ⟨some (α / γ), ?_⟩
        have hp' : α ^ 2 + α * γ + a * γ ^ 2 = 1 := hp
        have h1 : ((α / γ) ^ 2 + α / γ + a) * γ ^ 2 = 1 := by
          have : ((α / γ) ^ 2 + α / γ + a) * γ ^ 2 = α ^ 2 + α * γ + a * γ ^ 2 := by
            field_simp
          rw [this]
          exact hp'
        have hsq : β (α / γ) ^ 2 = γ ^ 2 := by
          rw [hβ]
          exact (eq_inv_of_mul_eq_one_right h1).symm
        have hb : β (α / γ) = γ := sq_injective_K _ _ hsq
        apply Subtype.ext
        show (α / γ * β (α / γ), β (α / γ)) = (α, γ)
        rw [hb]
        exact Prod.ext (div_mul_cancel₀ α hγ) rfl
  rw [← Finite.card_option]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem card_Tgrp [Finite K] (a : K) (ha : ∀ z : K, z ^ 2 + z + a ≠ 0) :
    Nat.card (Tgrp a) = Nat.card K + 1 := by
  rw [← card_nrm2_one a ha]
  refine Nat.card_congr
    { toFun := fun g => ⟨((g.1 : Matrix (Fin 2) (Fin 2) K) 0 0,
        (g.1 : Matrix (Fin 2) (Fin 2) K) 1 0), by
        obtain ⟨α, β, hn, hg⟩ := g.2
        have e0 : (g.1 : Matrix (Fin 2) (Fin 2) K) 0 0 = α := by rw [hg]; rfl
        have e1 : (g.1 : Matrix (Fin 2) (Fin 2) K) 1 0 = β := by rw [hg]; rfl
        show nrm2 a ((g.1 : Matrix (Fin 2) (Fin 2) K) 0 0)
          ((g.1 : Matrix (Fin 2) (Fin 2) K) 1 0) = 1
        rw [e0, e1]
        exact hn⟩
      invFun := fun p => ⟨rotGL a p.1.1 p.1.2 p.2, p.1.1, p.1.2, p.2, rfl⟩
      left_inv := fun g => by
        obtain ⟨α, β, hn, hg⟩ := g.2
        have e0 : (g.1 : Matrix (Fin 2) (Fin 2) K) 0 0 = α := by rw [hg]; rfl
        have e1 : (g.1 : Matrix (Fin 2) (Fin 2) K) 1 0 = β := by rw [hg]; rfl
        apply Subtype.ext
        apply Units.ext
        show rotM a ((g.1 : Matrix (Fin 2) (Fin 2) K) 0 0)
          ((g.1 : Matrix (Fin 2) (Fin 2) K) 1 0) = (g.1 : Matrix (Fin 2) (Fin 2) K)
        rw [e0, e1, hg]
      right_inv := fun p => by
        apply Subtype.ext
        show (rotM a p.1.1 p.1.2 0 0, rotM a p.1.1 p.1.2 1 0) = p.1
        simp [rotM] }

@[expose] def sM : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1]

theorem sM_mul_self : sM * sM = (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sM, Matrix.mul_apply, Fin.sum_univ_two, h2]

@[expose] def sGL : GL (Fin 2) K := ⟨sM, sM, sM_mul_self, sM_mul_self⟩

theorem sGL_val : (sGL : GL (Fin 2) K).val = sM := rfl

theorem sGL_inv_val : ((sGL : GL (Fin 2) K)⁻¹ : GL (Fin 2) K).val = sM := rfl

theorem sM_rot (a α β : K) : sM * rotM a α β * sM = rotM a (α + β) β := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sM, rotM, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (α + β) * h2

theorem planeNrm_sM (a : K) (p : Fin 2 → K) : planeNrm a (sM *ᵥ p) = planeNrm a p := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs : sM *ᵥ p = ![p 0 + p 1, p 1] := by
    ext i
    fin_cases i <;> simp [sM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hs]
  simp only [planeNrm, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (p 0 * p 1 + p 1 ^ 2) * h2

theorem Tgrp_inv_val (a : K) {g : GL (Fin 2) K} {α β : K} (hn : nrm2 a α β = 1)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = rotM a α β) :
    ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = rotM a (α + β) β := by
  have h1 : (g : Matrix (Fin 2) (Fin 2) K) * rotM a (α + β) β = 1 := by
    rw [hg]
    exact rotM_mul_inv a α β hn
  calc ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((g : Matrix (Fin 2) (Fin 2) K) * rotM a (α + β) β) := by rw [h1, Matrix.mul_one]
    _ = rotM a (α + β) β := by rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem sGL_conj (a : K) {g : GL (Fin 2) K} (hg : g ∈ Tgrp a) : sGL * g * sGL⁻¹ = g⁻¹ := by
  obtain ⟨α, β, hn, hgv⟩ := hg
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sGL_val, sGL_inv_val, hgv, sM_rot, Tgrp_inv_val a hn hgv]

@[expose] def planeIso (a : K) : Subgroup (GL (Fin 2) K) where
  carrier := {g | ∀ p, planeNrm a ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ p) = planeNrm a p}
  one_mem' := fun p => by simp
  mul_mem' := fun {g h} hg hh p => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg, hh]
  inv_mem' := fun {g} hg p => by
    have h1 := hg (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ p)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
    exact h1.symm

theorem Tgrp_le_planeIso (a : K) : Tgrp a ≤ planeIso a := by
  rintro g ⟨α, β, hn, hg⟩ p
  rw [hg, planeNrm_rot, hn, one_mul]

theorem sGL_mem_planeIso (a : K) : (sGL : GL (Fin 2) K) ∈ planeIso a := fun p => by
  rw [sGL_val]
  exact planeNrm_sM a p

theorem Tgrp_odd_mem_commutator (a : K) {r : ℕ} (hr : Odd r) {g : GL (Fin 2) K}
    (hg : g ∈ Tgrp a) (hgr : g ^ r = 1) : g ∈ ⁅planeIso a, planeIso a⁆ := by
  obtain ⟨m, rfl⟩ := hr
  have hh : g ^ (m + 1) ∈ Tgrp a := Subgroup.pow_mem _ hg _
  have hhh : g ^ (m + 1) * g ^ (m + 1) = g := by
    rw [← pow_add]
    have : m + 1 + (m + 1) = (2 * m + 1) + 1 := by ring
    rw [this, pow_succ, hgr, one_mul]
  have hcomm : ⁅g ^ (m + 1), (sGL : GL (Fin 2) K)⁆ = g ^ (m + 1) * g ^ (m + 1) := by
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc (sGL : GL (Fin 2) K)]
    rw [sGL_conj a (Subgroup.inv_mem _ hh), inv_inv]
  rw [← hhh, ← hcomm]
  exact Subgroup.commutator_mem_commutator (Tgrp_le_planeIso a hh) (sGL_mem_planeIso a)

end Plane

end CFSG.QuasithinUnique.Setup.Family

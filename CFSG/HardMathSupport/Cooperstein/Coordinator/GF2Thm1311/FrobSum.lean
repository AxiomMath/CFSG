module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open QuadraticMap

section F4
variable {K : Type*} [Field K] [CharP K 2]

theorem F4_pow_four [Finite K] (h : Nat.card K = 4) (x : K) : x ^ 4 = x := by
  have : Fintype K := Fintype.ofFinite K
  have h' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact h
  have := FiniteField.pow_card x
  rwa [h'] at this

theorem F4_sq_eq_self {x : K} (h : x ^ 2 = x) : x = 0 ∨ x = 1 := by
  have : x * (x - 1) = 0 := by rw [mul_sub, mul_one, ← _root_.sq, h, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · left; exact h
  · right; exact sub_eq_zero.mp h

theorem F4_trace_sq [Finite K] (h : Nat.card K = 4) (x : K) :
    (x ^ 2 + x) ^ 2 = x ^ 2 + x := by
  have h4 : (x ^ 2) ^ 2 = x := by rw [← pow_mul]; exact F4_pow_four h x
  rw [CharTwo.add_sq, h4, add_comm]

theorem F4_trace_cases [Finite K] (h : Nat.card K = 4) (x : K) :
    x ^ 2 + x = 0 ∨ x ^ 2 + x = 1 :=
  F4_sq_eq_self (F4_trace_sq h x)

theorem F4_exists_ne [Finite K] (h : Nat.card K = 4) : ∃ x : K, x ≠ 0 ∧ x ≠ 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact h
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [hcon x hx]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, h'] at this
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

theorem F4_exists_omega [Finite K] (h : Nat.card K = 4) : ∃ ω : K, ω ^ 2 + ω = 1 := by
  obtain ⟨x, hx0, hx1⟩ := F4_exists_ne h
  refine ⟨x, ?_⟩
  rcases F4_trace_cases h x with h0 | h1
  · exfalso
    have : x * (x + 1) = 0 := by rw [mul_add, mul_one, ← _root_.sq, h0]
    rcases mul_eq_zero.mp this with h | h
    · exact hx0 h
    · apply hx1
      have : x = -1 := eq_neg_of_add_eq_zero_left h
      rw [this, CharTwo.neg_eq]
  · exact h1

end F4

theorem add_self_eq_zero_module (K : Type*) {V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] (v : V) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

section Sum
variable {K V : Type*} [Field K] [CharP K 2] [Finite K] [AddCommGroup V] [Module K V]

open Classical in
@[expose] noncomputable def chi (x : K) : ℤ := if x ^ 2 + x = 0 then 1 else -1

@[expose] noncomputable def sgn (x : K) : ℤ := by classical exact if x = 0 then 1 else -1

theorem chi_add (h : Nat.card K = 4) (x y : K) : chi (x + y) = chi x * chi y := by
  unfold chi
  have hs : (x + y) ^ 2 + (x + y) = (x ^ 2 + x) + (y ^ 2 + y) := by
    rw [CharTwo.add_sq]; ring
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [hs]
  rcases F4_trace_cases h x with hx | hx <;> rcases F4_trace_cases h y with hy | hy <;>
    simp [hx, hy, h11]

theorem chi_of_mem {a : K} (ha : a = 0 ∨ a = 1) : chi a = 1 := by
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rcases ha with rfl | rfl <;> simp [chi, h11]

theorem chi_omega_mul (h : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω = 1) {b : K}
    (hb : b = 0 ∨ b = 1) : chi (ω * b) = sgn b := by
  rcases hb with rfl | rfl
  · simp [chi, sgn]
  · have : chi ω = -1 := by simp [chi, hω]
    simpa [sgn] using this

theorem chi_omega_sq_mul (h : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω = 1) {b : K}
    (hb : b = 0 ∨ b = 1) : chi (ω * ω * b) = sgn b := by
  rcases hb with rfl | rfl
  · simp [chi, sgn]
  · have h4 : (ω ^ 2) ^ 2 = ω := by rw [← pow_mul]; exact F4_pow_four h ω
    have : chi (ω * ω) = -1 := by
      have e : (ω * ω) ^ 2 + ω * ω = 1 := by
        rw [← _root_.sq, h4, add_comm]; exact hω
      simp [chi, e]
    simpa [sgn] using this

theorem sgn_add_one {x : K} (hx : x = 0 ∨ x = 1) : sgn (x + 1) = - sgn x := by
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rcases hx with rfl | rfl <;> simp [sgn, h11]

theorem polar_sq_of_T (σ : K →+* K) (Q : QuadraticForm K V) (T : V →ₛₗ[σ] V)
    (hσ : ∀ x, σ x = x ^ 2) (hTQ : ∀ v, Q (T v) = Q v ^ 2) (x y : V) :
    polar Q (T x) (T y) = polar Q x y ^ 2 := by
  unfold polar
  rw [← map_add, hTQ, hTQ, hTQ, CharTwo.sub_eq_add, CharTwo.sub_eq_add, CharTwo.sub_eq_add,
    CharTwo.sub_eq_add, CharTwo.add_sq, CharTwo.add_sq]

theorem sum_chi_pos [Fintype V] (hK : Nat.card K = 4) (Q : QuadraticForm K V) (σ : K →+* K)
    (hσ : ∀ x, σ x = x ^ 2) (T : V →ₛₗ[σ] V) (hTT : ∀ v, T (T v) = v)
    (hTQ : ∀ v, Q (T v) = Q v ^ 2) (hnd : ∀ w, (∀ v, polar Q v w = 0) → w = 0) :
    0 < ∑ v, chi (Q v) := by
  classical
  obtain ⟨ω, hω⟩ := F4_exists_omega hK
  have hω' : ω ^ 2 - ω = 1 := by rw [CharTwo.sub_eq_add]; exact hω
  have hTs : ∀ (c : K) v, T (c • v) = c ^ 2 • T v := fun c v => by rw [map_smulₛₗ, hσ]
  have h2 : ∀ v : V, v + v = 0 := add_self_eq_zero_module K
  let V0 := {u : V // T u = u}
  let Φ : V0 × V0 → V := fun p => p.1.1 + ω • p.2.1
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ ⟨⟨u', hu'⟩, ⟨w', hw'⟩⟩ h
      simp only [Φ] at h
      have h2' := congrArg T h
      rw [map_add, map_add, hTs, hTs, hu, hu', hw, hw'] at h2'
      have e : (ω ^ 2 - ω) • w = (ω ^ 2 - ω) • w' := by
        calc (ω ^ 2 - ω) • w = (u + ω ^ 2 • w) - (u + ω • w) := by module
          _ = (u' + ω ^ 2 • w') - (u' + ω • w') := by rw [h2', h]
          _ = (ω ^ 2 - ω) • w' := by module
      rw [hω', one_smul, one_smul] at e
      subst e
      have : u = u' := by simpa using h
      subst this
      rfl
    · intro v
      have hw : T (v + T v) = v + T v := by rw [map_add, hTT, add_comm]
      refine ⟨(⟨v + ω • (v + T v), ?_⟩, ⟨v + T v, hw⟩), ?_⟩
      · rw [map_add, hTs, hw]
        calc T v + ω ^ 2 • (v + T v)
            = (v + ω • (v + T v)) + (ω ^ 2 - ω) • (v + T v) + (T v - v) := by module
          _ = (v + ω • (v + T v)) + (1 : K) • (v + T v) + (T v - v) := by rw [hω']
          _ = (v + ω • (v + T v)) + (T v + T v) := by module
          _ = v + ω • (v + T v) := by rw [h2 (T v), add_zero]
      · simp only [Φ]
        calc v + ω • (v + T v) + ω • (v + T v) = v + (ω • (v + T v) + ω • (v + T v)) := by abel
          _ = v := by rw [h2, add_zero]
  have hQfix : ∀ u : V, T u = u → Q u = 0 ∨ Q u = 1 := fun u hu => by
    have := hTQ u
    rw [hu] at this
    exact F4_sq_eq_self this.symm
  have hBfix : ∀ u w : V, T u = u → T w = w → polar Q u w = 0 ∨ polar Q u w = 1 := by
    intro u w hu hw
    have := polar_sq_of_T σ Q T hσ hTQ u w
    rw [hu, hw] at this
    exact F4_sq_eq_self this.symm
  have hval : ∀ u w : V0, chi (Q (Φ (u, w))) = sgn (Q w.1) * sgn (polar Q u.1 w.1) := by
    rintro ⟨u, hu⟩ ⟨w, hw⟩
    simp only [Φ]
    have e : Q (u + ω • w) = Q u + ω * ω * Q w + ω * polar Q u w := by
      rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, smul_eq_mul,
        smul_eq_mul]
    rw [e, chi_add hK, chi_add hK, chi_of_mem (hQfix u hu),
      chi_omega_sq_mul hK hω (hQfix w hw), chi_omega_mul hK hω (hBfix u w hu hw)]
    ring
  have hinner : ∀ w : V0, ∑ u : V0, sgn (polar Q u.1 w.1) =
      if w.1 = 0 then (Fintype.card V0 : ℤ) else 0 := by
    intro w
    by_cases hw0 : w.1 = 0
    · simp [hw0, sgn]
    · rw [if_neg hw0]
      obtain ⟨u0, hu0⟩ : ∃ u0 : V0, polar Q u0.1 w.1 ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hw0
        apply hnd
        intro v
        obtain ⟨⟨u, u'⟩, rfl⟩ := hbij.2 v
        simp only [Φ]
        rw [polar_add_left, polar_smul_left, hcon u, hcon u']
        simp
      have hu01 : polar Q u0.1 w.1 = 1 := (hBfix _ _ u0.2 w.2).resolve_left hu0
      let e : V0 → V0 := fun u => ⟨u.1 + u0.1, by rw [map_add, u.2, u0.2]⟩
      have he : Function.Involutive e := fun u =>
        Subtype.ext (by simp only [e]; rw [add_assoc, h2, add_zero])
      have hsum := Fintype.sum_bijective e he.bijective
        (fun u : V0 => sgn (polar Q (e u).1 w.1)) (fun u : V0 => sgn (polar Q u.1 w.1))
        (fun _ => rfl)
      have hneg : ∑ u : V0, sgn (polar Q (e u).1 w.1) = -∑ u : V0, sgn (polar Q u.1 w.1) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        simp only [e]
        rw [polar_add_left, hu01]
        exact sgn_add_one (hBfix _ _ u.2 w.2)
      linarith
  have hS : ∑ v, chi (Q v) = ∑ p : V0 × V0, chi (Q (Φ p)) :=
    (Fintype.sum_bijective Φ hbij (fun p => chi (Q (Φ p))) (fun v => chi (Q v))
      (fun _ => rfl)).symm
  have hpos : (0 : ℤ) < Fintype.card V0 := by
    haveI : Nonempty V0 := ⟨⟨0, map_zero T⟩⟩
    exact_mod_cast Fintype.card_pos
  rw [hS, Fintype.sum_prod_type]
  simp_rw [hval]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hinner]
  rw [Finset.sum_eq_single (⟨0, map_zero T⟩ : V0)]
  · simpa [sgn] using hpos
  · intro w _ hw
    have : w.1 ≠ 0 := fun h => hw (Subtype.ext h)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Sum

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

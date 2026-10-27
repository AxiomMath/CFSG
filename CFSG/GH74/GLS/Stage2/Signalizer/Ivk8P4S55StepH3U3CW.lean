module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder
public import Mathlib.FieldTheory.ChevalleyWarning

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U3

open MvPolynomial CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open scoped Matrix

theorem totalDegree_sum_le {σ R ι : Type*} [CommSemiring R] (s : Finset ι)
    (P : ι → MvPolynomial σ R) {d : ℕ} (h : ∀ i ∈ s, (P i).totalDegree ≤ d) :
    (∑ i ∈ s, P i).totalDegree ≤ d :=
  (totalDegree_finsetSum s P).trans (Finset.sup_le h)

theorem totalDegree_C_mul_X_mul_X_le {σ R : Type*} [CommSemiring R] [Nontrivial R] (c : R)
    (a b : σ) : (C c * X a * X b : MvPolynomial σ R).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (C c * X a : MvPolynomial σ R).totalDegree ≤ 1 := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add, totalDegree_X]
  rw [totalDegree_X]
  omega

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_ne_zero_stdHermForm_mulVec_eq_zero (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) K) :
    ∃ v : Fin n → K, v ≠ 0 ∧ stdHermForm h n v (A *ᵥ v) = 0 := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hK : CharP K p := h.charP
  set F : Subfield K := h.fixedField with hFdef
  have hFmem : ∀ y : K, y ∈ F ↔ h.bar y = y := fun y => h.mem_fixedField
  have : Fintype ↥F := Fintype.ofFinite _
  have : CharP ↥F p := (F.subtype.charP_iff F.subtype.injective p).mpr hK
  have hbarF : ∀ y : ↥F, h.bar (y : K) = y := fun y => (hFmem _).1 y.2
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at h0'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp h0')
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  set ι : K := c₀ - h.bar c₀ with hιdef
  have hι0 : ι ≠ 0 := sub_ne_zero.mpr (Ne.symm hc₀)
  have hι : h.bar ι = -ι := by rw [hιdef, map_sub, h.bar_bar, neg_sub]
  have hbar2 : h.bar 2 = 2 := map_ofNat h.bar 2
  have hre : ∀ k : K, (k + h.bar k) / 2 ∈ F := fun k => by
    rw [hFmem, map_div₀, map_add, h.bar_bar, hbar2, add_comm]
  have him : ∀ k : K, (k - h.bar k) / (2 * ι) ∈ F := fun k => by
    rw [hFmem, map_div₀, map_sub, h.bar_bar, map_mul, hbar2, hι]
    field_simp
    ring
  let re : K → ↥F := fun k => ⟨_, hre k⟩
  let im : K → ↥F := fun k => ⟨_, him k⟩
  have hsplit : ∀ k t : K, k * t = (re k : K) * t + ι * ((im k : K) * t) := fun k t => by
    change k * t = (k + h.bar k) / 2 * t + ι * ((k - h.bar k) / (2 * ι) * t)
    field_simp
    ring
  let β : Fin 2 → K := ![1, -ι]
  let γ : Fin 2 → K := ![1, ι]
  let coef : Fin n → Fin n → Fin 2 → Fin 2 → K := fun i j a b => β a * A i j * γ b
  let v : (Fin n × Fin 2 → ↥F) → Fin n → K := fun x i => (x (i, 0) : K) + ι * (x (i, 1) : K)
  have hΦ : ∀ x, stdHermForm h n (v x) (A *ᵥ v x) =
      ∑ i, ∑ j, ∑ a, ∑ b, coef i j a b * ((x (i, a) : K) * (x (j, b) : K)) := by
    intro x
    rw [stdHermForm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hb : h.bar (v x i) = (x (i, 0) : K) + (-ι) * (x (i, 1) : K) := by
      change h.bar ((x (i, 0) : K) + ι * (x (i, 1) : K)) = _
      rw [map_add, map_mul, hbarF, hbarF, hι]
    rw [hb, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [coef, β, γ, v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  let P₁ : MvPolynomial (Fin n × Fin 2) ↥F :=
    ∑ i, ∑ j, ∑ a, ∑ b, C (re (coef i j a b)) * X (i, a) * X (j, b)
  let P₂ : MvPolynomial (Fin n × Fin 2) ↥F :=
    ∑ i, ∑ j, ∑ a, ∑ b, C (im (coef i j a b)) * X (i, a) * X (j, b)
  have heval : ∀ (g : K → ↥F) (x : Fin n × Fin 2 → ↥F),
      ((eval x (∑ i, ∑ j, ∑ a, ∑ b, C (g (coef i j a b)) * X (i, a) * X (j, b)) : ↥F) : K) =
        ∑ i, ∑ j, ∑ a, ∑ b, (g (coef i j a b) : K) * ((x (i, a) : K) * (x (j, b) : K)) := by
    intro g x
    simp only [map_sum, map_mul, eval_C, eval_X]
    push_cast
    simp only [mul_assoc]
  have hdeg : ∀ g : K → ↥F,
      (∑ i, ∑ j, ∑ a, ∑ b, C (g (coef i j a b)) * X (i, a) * X (j, b) :
        MvPolynomial (Fin n × Fin 2) ↥F).totalDegree ≤ 2 := fun g =>
    totalDegree_sum_le _ _ fun i _ => totalDegree_sum_le _ _ fun j _ =>
      totalDegree_sum_le _ _ fun a _ => totalDegree_sum_le _ _ fun b _ =>
        totalDegree_C_mul_X_mul_X_le _ _ _
  have hzero : ∀ x, eval x P₁ = 0 → eval x P₂ = 0 → stdHermForm h n (v x) (A *ᵥ v x) = 0 := by
    intro x h1 h2'
    have e1 := heval re x
    have e2 := heval im x
    rw [h1] at e1
    rw [h2'] at e2
    rw [hΦ]
    have hsum : ∑ i, ∑ j, ∑ a, ∑ b, coef i j a b * ((x (i, a) : K) * (x (j, b) : K)) =
        ∑ i, ∑ j, ∑ a, ∑ b, (re (coef i j a b) : K) * ((x (i, a) : K) * (x (j, b) : K)) +
          ι * ∑ i, ∑ j, ∑ a, ∑ b, (im (coef i j a b) : K) * ((x (i, a) : K) * (x (j, b) : K)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      exact hsplit _ _
    rw [hsum, ← e1, ← e2]
    simp
  have hcard : Fintype.card (Fin n × Fin 2) = n * 2 := by simp
  have hlt : P₁.totalDegree + P₂.totalDegree < Fintype.card (Fin n × Fin 2) := by
    have hd1 : P₁.totalDegree ≤ 2 := hdeg re
    have hd2 : P₂.totalDegree ≤ 2 := hdeg im
    rw [hcard]
    omega
  have hdvd := char_dvd_card_solutions_of_add_lt p hlt
  have h0 : eval (0 : Fin n × Fin 2 → ↥F) P₁ = 0 ∧ eval (0 : Fin n × Fin 2 → ↥F) P₂ = 0 := by
    simp [P₁, P₂]
  have hpos : 0 < Fintype.card
      {x : Fin n × Fin 2 → ↥F // eval x P₁ = 0 ∧ eval x P₂ = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have h1lt : 1 < Fintype.card {x : Fin n × Fin 2 → ↥F // eval x P₁ = 0 ∧ eval x P₂ = 0} :=
    lt_of_lt_of_le h.prime.one_lt (Nat.le_of_dvd hpos hdvd)
  obtain ⟨⟨x, hx⟩, hx0⟩ := Fintype.exists_ne_of_one_lt_card h1lt ⟨0, h0⟩
  refine ⟨v x, ?_, hzero x hx.1 hx.2⟩
  intro hv
  apply hx0
  apply Subtype.ext
  funext ⟨i, a⟩
  have hvi : (x (i, 0) : K) + ι * (x (i, 1) : K) = 0 := congrFun hv i
  have hvb : (x (i, 0) : K) + (-ι) * (x (i, 1) : K) = 0 := by
    have := congrArg h.bar hvi
    rwa [map_add, map_mul, hbarF, hbarF, hι, map_zero] at this
  have hx0' : (x (i, 0) : K) = 0 := by
    have : 2 * (x (i, 0) : K) = 0 := by linear_combination hvi + hvb
    exact (mul_eq_zero.mp this).resolve_left h2
  have hx1' : (x (i, 1) : K) = 0 := by
    have : (2 * ι) * (x (i, 1) : K) = 0 := by linear_combination hvi - hvb
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hι0)
  fin_cases a
  · exact Subtype.ext hx0'
  · exact Subtype.ext hx1'

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U3

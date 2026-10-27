module

import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L5HeisCore
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3HeisNum
import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial

theorem uq5hn_fixed_false {p f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {t : ℕ} (ht : t.Prime) (ht2 : t ≠ 2)
    (ht5 : t ≠ 5) (τ : K ≃+* K) (hτ : orderOf τ = t) {w : K} (hw0 : w ≠ 0) (hwτ : τ w = w)
    (hord : 5 * orderOf w = p ^ f + 1) : False := by
  obtain ⟨hdvd, hcard, -⟩ := CFSG.RankThree.UnitaryDescent.fixed_field_facts h ht ht2 τ hτ
  have hpp : p.Prime := h.prime
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    omega
  have hf1 : 1 ≤ f := h.one_le
  have := Fintype.ofFinite
    (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield τ)
  let w' : CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield τ :=
    ⟨w, RingHom.mem_eqLocusField.mpr hwτ⟩
  have hw'0 : w' ≠ 0 := fun h0 => hw0 (congrArg Subtype.val h0)
  have hpow := FiniteField.pow_card_sub_one_eq_one w' hw'0
  rw [← Nat.card_eq_fintype_card, hcard] at hpow
  have hpow' : w ^ ((p ^ (f / t)) ^ 2 - 1) = 1 := congrArg Subtype.val hpow
  have hht : f / t ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) ht.pos
    omega
  have hT3 : 3 ≤ p ^ (f / t) := hp3.trans (Nat.le_self_pow hht p)
  have hTodd : Odd (p ^ (f / t)) := (hpp.eq_two_or_odd'.resolve_left hp2).pow
  have hq : p ^ f = (p ^ (f / t)) ^ t := by
    rw [← pow_mul, Nat.div_mul_cancel hdvd]
  have hdvd' := orderOf_dvd_of_pow_eq_one hpow'
  generalize p ^ (f / t) = T at hT3 hTodd hdvd' hq
  have h9 : 9 ≤ T ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ T ^ 2 := Nat.pow_le_pow_left hT3 2
  have hle : orderOf w ≤ T ^ 2 - 1 := Nat.le_of_dvd (by omega) hdvd'
  rw [hq] at hord
  have ht37 : t = 3 ∨ 7 ≤ t := by
    have h2 := ht.two_le
    by_contra hcon
    have h6 : t < 7 := by omega
    interval_cases t <;> first | omega | (norm_num at ht)
  rcases ht37 with rfl | h7
  · have hT4 : T ≤ 4 := by
      by_contra hlt
      have h5 : 5 ≤ T := by omega
      have h5T : 5 * T ^ 2 ≤ T * T ^ 2 := Nat.mul_le_mul_right _ h5
      have e : T ^ 3 = T * T ^ 2 := by ring
      omega
    obtain ⟨k, hk⟩ := hTodd
    have hT : T = 3 := by omega
    subst hT
    omega
  · have h243 : 243 ≤ T ^ 5 := by
      calc 243 = 3 ^ 5 := by norm_num
        _ ≤ T ^ 5 := Nat.pow_le_pow_left hT3 5
    have h7T : T ^ 7 ≤ T ^ t := Nat.pow_le_pow_right (by omega) h7
    have hmul : 243 * T ^ 2 ≤ T ^ 5 * T ^ 2 := Nat.mul_le_mul_right _ h243
    have e : T ^ 7 = T ^ 5 * T ^ 2 := by ring
    omega

theorem uq5_heis_torus_contra {p f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (h5 : 5 ∣ p ^ f + 1) {t : ℕ} (ht : t.Prime)
    (ht2 : t ≠ 2) (ht5 : t ≠ 5) (τ : K ≃+* K) (hτ : orderOf τ = t) (s : Kˣ)
    (hs : orderOf s = p ^ f + 1) (X : GL (Fin 5) K) (lam : K)
    (hmat : (X : Matrix (Fin 5) (Fin 5) K) *
        Matrix.diagonal ![τ (s : K) ^ 5, (τ (s : K) ^ 5)⁻¹, 1, 1, 1] *
        ((X⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      lam • Matrix.diagonal ![(s : K) ^ 5, ((s : K) ^ 5)⁻¹, 1, 1, 1]) : False := by
  classical
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hw0 : (s : K) ^ 5 ≠ 0 := pow_ne_zero 5 hs0
  have hτw0 : τ (s : K) ^ 5 ≠ 0 := pow_ne_zero 5 ((map_ne_zero τ).mpr hs0)
  have hsq : (s : K) ^ (p ^ f + 1) = 1 := by
    have h1 := pow_orderOf_eq_one s
    rw [hs] at h1
    simpa using congrArg Units.val h1
  have hso : orderOf (s : K) = p ^ f + 1 := by rw [orderOf_units, hs]
  have hord : 5 * orderOf ((s : K) ^ 5) = p ^ f + 1 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hso]; exact h5), hso]
    exact Nat.mul_div_cancel' h5
  have hlam : lam = 1 := Ln.eq_one_of_conj_diag_five X _ _ _ _ _ hmat
  rw [hlam, one_smul] at hmat
  rcases Ln.trace_argument_five X hτw0 hw0 hmat with h1 | h2
  · exact uq5hn_fixed_false h hp2 ht ht2 ht5 τ hτ hw0 (by rw [map_pow]; exact h1) hord
  · have hwq : ((s : K) ^ 5) ^ (p ^ f + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hsq, one_pow]
    have hbar : h.bar ((s : K) ^ 5) = ((s : K) ^ 5)⁻¹ := by
      rw [h.bar_apply]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      exact hwq
    have hτw : τ ((s : K) ^ 5) = h.bar ((s : K) ^ 5) := by
      rw [hbar, map_pow]
      exact eq_inv_of_mul_eq_one_left h2
    have hcomm : ∀ x : K, τ (h.bar x) = h.bar (τ x) := by
      intro x
      simp only [h.bar_apply, map_pow]
    have hττ : τ (τ ((s : K) ^ 5)) = (s : K) ^ 5 := by
      rw [hτw, hcomm, hτw, h.bar_bar]
    exact uq5hn_fixed_false h hp2 ht ht2 ht5 τ hτ hw0
      (u3hn_fix τ hτ (ht.eq_two_or_odd'.resolve_left ht2) hττ) hord

end CFSG.GH74.GLS.Stage2.Bender.Thm1

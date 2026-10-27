module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Abel
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open Subgroup

variable {X : Type} [Group X]

private def omegaPsi (c v : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 :=
  ![v 0 + v 1 + v 4 * c 0, v 0 + v 4 * c 1, v 2 + v 4 * c 2, v 3 + v 4 * c 3, v 4 * c 4]

private theorem omegaPsi_step1 (c0 c1 c2 c3 : ZMod 2) :
    omegaPsi ![c0, c1, c2, c3, 0] ![c1, c0 + c1, c2, c3, 1] = 0 := by
  revert c0 c1 c2 c3
  decide

private theorem omegaPsi_step2 (c0 c1 c2 c3 : ZMod 2) :
    omegaPsi ![c0, c1, c2, c3, 1] (omegaPsi ![c0, c1, c2, c3, 1] ![c0, c1, c2, c3, 1]) =
      ![0, 0, c2, c3, 1] := by
  revert c0 c1 c2 c3
  decide

private theorem omegaPsi_cube (c : Fin 5 → ZMod 2) (a b d e : ZMod 2) :
    omegaPsi c (omegaPsi c (omegaPsi c ![a, b, d, e, 0])) = ![a, b, d, e, 0] := by
  simp [omegaPsi]
  revert a b d e
  decide

private theorem omegaConj {g : Fin 5 → X} (hg : IsE5 g) {ν : X} {c : Fin 5 → ZMod 2}
    (h0 : ν * g 0 * ν⁻¹ = g 0 * g 1) (h1 : ν * g 1 * ν⁻¹ = g 0)
    (h2 : ν * g 2 * ν⁻¹ = g 2) (h3 : ν * g 3 * ν⁻¹ = g 3)
    (h4 : ν * g 4 * ν⁻¹ = mono g c) (v : Fin 5 → ZMod 2) :
    ν * mono g v * ν⁻¹ = mono g (omegaPsi c v) := by
  have hcc : ∀ i, ν * g i * ν⁻¹ = mono g
      ((![Pi.single 0 1 + Pi.single 1 1, Pi.single 0 1, Pi.single 2 1, Pi.single 3 1, c] :
        Fin 5 → Fin 5 → ZMod 2) i) := by
    intro i
    fin_cases i
    · simp [hg.mono_add, hg.mono_single, h0]
    · simp [hg.mono_single, h1]
    · simp [hg.mono_single, h2]
    · simp [hg.mono_single, h3]
    · simpa using h4
  rw [hg.conj_mono ν _ hcc v]
  congr 1
  funext j
  fin_cases j <;> simp [omegaPsi, Fin.sum_univ_five, Pi.single_apply]

private theorem omegaConjPow3 (ν y : X) :
    ν ^ 3 * y * (ν ^ 3)⁻¹ = ν * (ν * (ν * y * ν⁻¹) * ν⁻¹) * ν⁻¹ := by
  simp only [pow_three', mul_inv_rev, mul_assoc]

private theorem omegaConjPow2 (ν y : X) : ν ^ 2 * y * (ν ^ 2)⁻¹ = ν * (ν * y * ν⁻¹) * ν⁻¹ := by
  simp only [pow_two, mul_inv_rev, mul_assoc]

private theorem omegaConj3 {g : Fin 5 → X} {ν : X} {c : Fin 5 → ZMod 2}
    (hψ : ∀ v, ν * mono g v * ν⁻¹ = mono g (omegaPsi c v)) (v : Fin 5 → ZMod 2) :
    ν ^ 3 * mono g v * (ν ^ 3)⁻¹ = mono g (omegaPsi c (omegaPsi c (omegaPsi c v))) := by
  rw [omegaConjPow3, hψ, hψ, hψ]

private theorem omegaCommute {z y : X} (h : z * y * z⁻¹ = y) : Commute z y :=
  mul_inv_eq_iff_eq_mul.mp h

private theorem omegaPowConj {y a z : X} (hb : z * y * z⁻¹ = y * a) (hc : z * a * z⁻¹ = a)
    (j : ℕ) : z ^ j * y * (z ^ j)⁻¹ = y * a ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : z ^ (j + 1) * y * (z ^ (j + 1))⁻¹ = z * (z ^ j * y * (z ^ j)⁻¹) * z⁻¹ := by
      simp only [pow_succ', mul_inv_rev, mul_assoc]
    have e' : z * (y * a ^ j) * z⁻¹ = (z * y * z⁻¹) * (z * a ^ j * z⁻¹) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [e, ih, e', hb, ← conj_pow, hc, mul_assoc, ← pow_succ']

theorem omega_fix [Finite X] {g : Fin 5 → X} (hg : IsE5 g) (hinj : Function.Injective (mono g))
    {ν : X} (hodd : Odd (orderOf ν))
    (hν : ν * g 1 * ν⁻¹ = g 0 ∧ ν * g 0 * ν⁻¹ = g 0 * g 1 ∧ ν * g 2 * ν⁻¹ = g 2 ∧
      ν * g 3 * ν⁻¹ = g 3)
    (hνx : ν * g 4 * ν⁻¹ ∈ Subgroup.closure (Set.range g)) :
    ∃ v : Fin 5 → ZMod 2, v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ ν * g 4 * ν⁻¹ = g 4 * mono g v := by
  obtain ⟨h1, h0, h2, h3⟩ := hν
  obtain ⟨c, hc⟩ := (hg.mem_closure_iff _).mp hνx
  have hψ := omegaConj hg h0 h1 h2 h3 hc
  have hc4 : c 4 = 1 := by
    by_contra hne
    have hc40 : c 4 = 0 := by
      generalize c 4 = a at hne ⊢
      revert a
      decide
    obtain ⟨c0, c1, c2, c3, rfl⟩ : ∃ c0 c1 c2 c3 : ZMod 2, c = ![c0, c1, c2, c3, 0] :=
      ⟨c 0, c 1, c 2, c 3, by funext i; fin_cases i <;> simp [hc40]⟩
    have h := hψ ![c1, c0 + c1, c2, c3, 1]
    rw [omegaPsi_step1, hg.mono_zero, conj_eq_one_iff] at h
    have h' := hinj (h.trans hg.mono_zero.symm)
    have := congrFun h' 4
    simp at this
  obtain ⟨c0, c1, c2, c3, rfl⟩ : ∃ c0 c1 c2 c3 : ZMod 2, c = ![c0, c1, c2, c3, 1] :=
    ⟨c 0, c 1, c 2, c 3, by funext i; fin_cases i <;> simp [hc4]⟩
  have hcube : ∀ a b d e : ZMod 2,
      ν ^ 3 * mono g ![a, b, d, e, 0] * (ν ^ 3)⁻¹ = mono g ![a, b, d, e, 0] := by
    intro a b d e
    rw [omegaConj3 hψ, omegaPsi_cube]
  have hz1 : Commute (ν ^ 3) (g 1) := by
    have := hcube 0 1 0 0
    rw [show (![0, 1, 0, 0, 0] : Fin 5 → ZMod 2) = Pi.single 1 1 by decide,
      hg.mono_single] at this
    exact omegaCommute this
  have hne01 : g 0 ≠ g 1 := by
    intro h
    have h' : mono g (Pi.single 0 1) = mono g (Pi.single 1 1) := by
      rw [hg.mono_single, hg.mono_single]
      exact h
    have := congrFun (hinj h') 0
    simp at this
  have hne0 : g 0 ≠ 1 := by
    intro h
    have h' : mono g (Pi.single 0 1) = mono g 0 := by
      rw [hg.mono_single, hg.mono_zero]
      exact h
    have := congrFun (hinj h') 0
    simp at this
  have h3m : 3 ∣ orderOf ν := by
    by_contra hnd
    have hdm : (ν ^ 3) ^ (orderOf ν / 3) * ν ^ (orderOf ν % 3) = 1 := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      exact pow_orderOf_eq_one ν
    have hrinv : ν ^ (orderOf ν % 3) = ((ν ^ 3) ^ (orderOf ν / 3))⁻¹ :=
      eq_inv_of_mul_eq_one_right hdm
    have hcom : Commute (ν ^ (orderOf ν % 3)) (g 1) := by
      rw [hrinv]
      exact (hz1.pow_left _).inv_left
    rcases (by omega : orderOf ν % 3 = 1 ∨ orderOf ν % 3 = 2) with hr | hr
    · rw [hr, pow_one] at hcom
      have := hcom.mul_inv_cancel
      rw [h1] at this
      exact hne01 this
    · rw [hr] at hcom
      have := hcom.mul_inv_cancel
      rw [omegaConjPow2, h1, h0] at this
      apply hne0
      simpa using this
  obtain ⟨j, hj⟩ := h3m
  have hjodd : j % 2 = 1 := by
    have := Nat.odd_iff.mp hodd
    omega
  have hzj : (ν ^ 3) ^ j = 1 := by
    rw [← pow_mul, ← hj]
    exact pow_orderOf_eq_one ν
  have hz4 : ν ^ 3 * g 4 * (ν ^ 3)⁻¹ = g 4 * mono g ![0, 0, c2, c3, 0] := by
    rw [omegaConjPow3, hc, hψ, hψ, omegaPsi_step2]
    have : (![0, 0, c2, c3, 1] : Fin 5 → ZMod 2) = Pi.single 4 1 + ![0, 0, c2, c3, 0] := by
      funext i
      fin_cases i <;> simp
    rw [this, hg.mono_add, hg.mono_single]
  have hza : ν ^ 3 * mono g ![0, 0, c2, c3, 0] * (ν ^ 3)⁻¹ = mono g ![0, 0, c2, c3, 0] :=
    hcube 0 0 c2 c3
  have hfj := omegaPowConj hz4 hza j
  rw [hzj] at hfj
  have hpow : mono g ![0, 0, c2, c3, 0] ^ j = mono g ![0, 0, c2, c3, 0] := by
    have h2 : mono g ![0, 0, c2, c3, 0] ^ 2 = 1 := by
      rw [pow_two]
      exact hg.mono_self _
    rw [pow_eq_pow_mod j h2, hjodd, pow_one]
  rw [hpow] at hfj
  have ha1 : mono g ![0, 0, c2, c3, 0] = 1 := by
    have : g 4 * mono g ![0, 0, c2, c3, 0] = g 4 * 1 := by
      rw [← hfj]
      simp
    exact mul_left_cancel this
  have hu : (![0, 0, c2, c3, 0] : Fin 5 → ZMod 2) = 0 := hinj (ha1.trans hg.mono_zero.symm)
  have hc2 : c2 = 0 := by simpa using congrFun hu 2
  have hc3 : c3 = 0 := by simpa using congrFun hu 3
  subst hc2 hc3
  refine ⟨![c0, c1, 0, 0, 0], rfl, rfl, rfl, ?_⟩
  rw [hc]
  have : (![c0, c1, 0, 0, 1] : Fin 5 → ZMod 2) = Pi.single 4 1 + ![c0, c1, 0, 0, 0] := by
    funext i
    fin_cases i <;> simp
  rw [this, hg.mono_add, hg.mono_single]

end CFSG.ComponentClassification.SolMax.Sig36.E32

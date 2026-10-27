module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU unitaryPSU)
open CFSG.Timmesfeld (IsPrimitivePrimeDivisor exists_isPrimitivePrimeDivisor)

theorem card_unitaryPSU_dvd_card_fixedSubgroup {n f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) {F : Type}
    [Field F] (hF : Nat.card F = 2 ^ (2 * f)) (A : GL (Fin n) F) {ρ : F ≃+* F} (hρ : ρ ≠ 1)
    (hθ : (conjAut n F A * fieldAut n F ρ * dualAut n F) *
        (conjAut n F A * fieldAut n F ρ * dualAut n F) = 1) :
    ∃ h : UnitaryFieldData 2 f F, Nat.card (unitaryPSU h n) ∣
      Nat.card (fixedSubgroup (conjAut n F A * fieldAut n F ρ * dualAut n F)) := by
  obtain ⟨-, hρx, H, hH⟩ := UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two
    (by omega : 1 ≤ 2 * f) hF hn A ρ hρ (by rw [sq]; exact hθ)
  have hud : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, hF⟩
  have := hud.finite
  have hσ : ∀ x, ρ x = hud.bar x := fun x => by
    rw [hρx, UnitaryFieldData.bar_apply, show 2 * f / 2 = f by omega]
  refine ⟨hud, ?_⟩
  rw [hH, card_fixedSubgroup_conjAut_mul]
  obtain ⟨E, -⟩ := exists_unitaryCoreEquiv hud hn ρ hσ
  rw [Nat.card_congr E.toEquiv]
  have hfix : autFixSubgroup (fieldAut n F ρ * dualAut n F) =
      fixedSubgroup (fieldAut n F ρ * dualAut n F) := by
    ext x
    rfl
  rw [← hfix]
  exact Subgroup.card_dvd_of_le (unitaryCore_le_autFixSubgroup hud hn ρ hσ)

section Unitary

variable {n e : ℕ} {F : Type} [Field F]

theorem dvd_card_unitarySU_of_dvd_pow_add_one (h : UnitaryFieldData 2 e F) (hn : 1 ≤ n) {j p : ℕ}
    (hj : Odd j) (hj2 : 2 ≤ j) (hjn : j ≤ n) (hp : p ∣ 2 ^ (e * j) + 1) :
    p ∣ Nat.card (unitarySU 2 e F n) := by
  have hSU := (card_unitarySU_and_factorization h hn).1
  have hz : ((p : ℕ) : ℤ) ∣ (Nat.card (unitarySU 2 e F n) : ℤ) := by
    rw [hSU]
    refine Dvd.dvd.mul_left ?_ _
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨hj2, hjn⟩))
    rw [hj.neg_one_pow, sub_neg_eq_add]
    have hcast : ((2 ^ e : ℕ) : ℤ) ^ j + 1 = ((2 ^ (e * j) + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast]
    exact Int.natCast_dvd_natCast.2 hp
  exact Int.natCast_dvd_natCast.1 hz

theorem dvd_card_unitaryPSU_of_ppd (h : UnitaryFieldData 2 e F) (hn : 1 ≤ n) {j p : ℕ}
    (hp : IsPrimitivePrimeDivisor p (2 * e * j)) (hj : Odd j) (hj2 : 2 ≤ j) (hjn : j ≤ n) :
    p ∣ Nat.card (unitaryPSU h n) := by
  have he := h.one_le
  have hk0 : 0 < 2 * e * j := by positivity
  have hp1 : p ∣ 2 ^ (e * j) + 1 := by
    refine (hp.dvd_add_one_iff hk0 (e * j)).2 ⟨⟨1, by ring⟩, ?_⟩
    exact Nat.not_dvd_of_pos_of_lt (by positivity) (by nlinarith)
  have hpSU := dvd_card_unitarySU_of_dvd_pow_add_one h hn hj hj2 hjn hp1
  rw [← card_unitaryPSU_mul h hn] at hpSU
  rcases (Nat.Prime.dvd_mul hp.prime).1 hpSU with h1 | h1
  · exact h1
  · exfalso
    have h2 : p ∣ 2 ^ e + 1 := h1.trans (Nat.gcd_dvd_right _ _)
    have h3 := (hp.dvd_add_one_iff hk0 e).1 h2
    have h4 := Nat.le_of_dvd (by omega) h3.1
    nlinarith

end Unitary

section Exclusion

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem not_card_unitaryPSU_dvd_of_two {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)
    (hK : Nat.card K = 2 ^ 1) (hn : n = 3 ∨ n = 4) :
    ¬ Nat.card (unitaryPSU h n) ∣ 2 * Nat.card (MulAut (projectiveSL n K)) := by
  intro hdvd
  have hn3 : 3 ≤ n := by omega
  have hA := Nat.mul_dvd_mul_left 2 (card_mulAut_projectiveSL_dvd hn3 hK)
  rw [card_GL_eq, hK] at hA
  have hSU := (card_unitarySU_and_factorization h (by omega : 1 ≤ n)).1
  have hPSU := card_unitaryPSU_mul h (by omega : 1 ≤ n)
  rcases hn with rfl | rfl
  · have h1 : (Nat.card (unitarySU 2 1 F 3) : ℤ) = 216 := by rw [hSU]; decide
    have h2 : Nat.card (unitaryPSU h 3) = 72 := by
      have h3 : Nat.gcd 3 (2 ^ 1 + 1) = 3 := by decide
      rw [h3] at hPSU
      omega
    have h4 : (2 : ℕ) ^ 1 = 2 := rfl
    rw [h2] at hdvd
    have h5 := hdvd.trans hA
    revert h5
    decide
  · have h1 : (Nat.card (unitarySU 2 1 F 4) : ℤ) = 25920 := by rw [hSU]; decide
    have h2 : Nat.card (unitaryPSU h 4) = 25920 := by
      have h3 : Nat.gcd 4 (2 ^ 1 + 1) = 1 := by decide
      rw [h3, mul_one] at hPSU
      omega
    rw [h2] at hdvd
    have h5 := hdvd.trans hA
    revert h5
    decide

theorem not_card_unitaryPSU_dvd_two_mul_card_mulAut (hn : 3 ≤ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {F : Type} [Field F] (h : UnitaryFieldData 2 f F) :
    ¬ Nat.card (unitaryPSU h n) ∣ 2 * Nat.card (MulAut (projectiveSL n K)) := by
  obtain ⟨j, hjodd, hj3, hjn, hj2, hnj⟩ :
      ∃ j, Odd j ∧ 3 ≤ j ∧ j ≤ n ∧ n < 2 * j ∧ n ≤ j + 1 := by
    rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩
    · exact ⟨n - 1, ⟨r - 1, by omega⟩, by omega, by omega, by omega, by omega⟩
    · exact ⟨n, ⟨r, hr⟩, hn, le_rfl, by omega, by omega⟩
  by_cases hexc : f = 1 ∧ j = 3
  · obtain ⟨rfl, rfl⟩ := hexc
    have hn34 : n = 3 ∨ n = 4 := by omega
    exact not_card_unitaryPSU_dvd_of_two h hK hn34
  · intro hdvd
    have hk2 : 2 ≤ 2 * f * j := by nlinarith
    have hk6 : 2 * f * j ≠ 6 := by
      intro h6
      have hfj : 2 * (f * j) = 6 := by rw [← h6]; ring
      have h1 : f * 3 ≤ f * j := Nat.mul_le_mul_left f hj3
      have hf1 : f = 1 := by omega
      subst hf1
      exact hexc ⟨rfl, by omega⟩
    obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor hk2 hk6
    have hpPSU := dvd_card_unitaryPSU_of_ppd h (by omega) hp hjodd (by omega) hjn
    have hfn : f * n < 2 * f * j := by nlinarith
    exact not_dvd_two_mul_card_mulAut_of_ppd hn hf hK hp hfn (hpPSU.trans hdvd)

end Exclusion

theorem not_card_fixedSubgroup_graphField_dvd {n f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) {K F : Type}
    [Field K] [Finite K] [Field F] (hK : Nat.card K = 2 ^ f) (hF : Nat.card F = 2 ^ (2 * f))
    (A : GL (Fin n) F) {ρ : F ≃+* F} (hρ : ρ ≠ 1)
    (hθ : (conjAut n F A * fieldAut n F ρ * dualAut n F) *
        (conjAut n F A * fieldAut n F ρ * dualAut n F) = 1) :
    ¬ Nat.card (fixedSubgroup (conjAut n F A * fieldAut n F ρ * dualAut n F)) ∣
      2 * Nat.card (MulAut (projectiveSL n K)) := by
  obtain ⟨h, hdvd⟩ := card_unitaryPSU_dvd_card_fixedSubgroup hf hn hF A hρ hθ
  exact fun h1 => not_card_unitaryPSU_dvd_two_mul_card_mulAut hn hf hK h (hdvd.trans h1)

theorem graphFieldInvolutionExclusion {n f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) {K F : Type}
    [Field K] [Finite K] [Field F] (hK : Nat.card K = 2 ^ f) (hF : Nat.card F = 2 ^ (2 * f)) :
    GraphFieldInvolutionExclusion n K F := by
  intro A ρ hρ hθ h1
  exact absurd h1 (not_card_fixedSubgroup_graphField_dvd hf hn hK hF A hρ hθ)

end CFSG.SeitzReduction.LinearPilot

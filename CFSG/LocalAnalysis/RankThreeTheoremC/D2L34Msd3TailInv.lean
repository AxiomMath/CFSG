module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

theorem sq_eq_inv_of_order_four {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hE : Nat.card E = 9) {t : X} (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (h4 : ∀ e ∈ E, t ^ 4 * e * (t ^ 4)⁻¹ = e)
    (h2 : ∃ e ∈ E, t ^ 2 * e * (t ^ 2)⁻¹ ≠ e) :
    ∀ e ∈ E, t ^ 2 * e * (t ^ 2)⁻¹ = e⁻¹ := by
  obtain ⟨φ, hφ⟩ : ∃ φ : X → X, ∀ x, φ x = t ^ 2 * x * (t ^ 2)⁻¹ := ⟨_, fun _ => rfl⟩
  have hφmul : ∀ x y, φ (x * y) = φ x * φ y := fun x y => by simp only [hφ]; group
  have hφinv : ∀ x, φ x⁻¹ = (φ x)⁻¹ := fun x => by simp only [hφ]; group
  have hφt : ∀ x, φ (t * x * t⁻¹) = t * φ x * t⁻¹ := fun x => by simp only [hφ]; group
  have hφE : ∀ e ∈ E, φ e ∈ E := by
    intro e he
    have h := htE _ (htE e he)
    have h' : t * (t * e * t⁻¹) * t⁻¹ = φ e := by rw [hφ, sq]; group
    rwa [h'] at h
  have hφφ : ∀ e ∈ E, φ (φ e) = e := by
    intro e he
    have h' : φ (φ e) = t ^ 4 * e * (t ^ 4)⁻¹ := by simp only [hφ]; group
    rw [h']
    exact h4 e he
  obtain ⟨S, hS⟩ : ∃ S : Subgroup X, ∀ x, x ∈ S ↔ x ∈ E ∧ φ x = x⁻¹ := by
    refine ⟨{ carrier := {x | x ∈ E ∧ φ x = x⁻¹}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · rintro a b ⟨haE, ha⟩ ⟨hbE, hb⟩
      refine ⟨E.mul_mem haE hbE, ?_⟩
      have hab := hEab a haE b hbE
      rw [hφmul, ha, hb]
      calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
        _ = (a * b)⁻¹ := by rw [hab]
    · refine ⟨E.one_mem, ?_⟩
      have h1 : φ 1 = 1 := by simp only [hφ]; group
      rw [h1, inv_one]
    · rintro a ⟨haE, ha⟩
      refine ⟨E.inv_mem haE, ?_⟩
      rw [hφinv, ha]
  have hSE : S ≤ E := fun s hs => ((hS s).1 hs).1
  obtain ⟨e, heE, hne⟩ := h2
  have hne' : φ e ≠ e := by rwa [hφ]
  obtain ⟨a, haE, haS, ha1⟩ : ∃ a : X, a ∈ E ∧ a ∈ S ∧ a ≠ 1 := by
    refine ⟨e * (φ e)⁻¹, E.mul_mem heE (E.inv_mem (hφE e heE)), ?_, ?_⟩
    · refine (hS _).2 ⟨E.mul_mem heE (E.inv_mem (hφE e heE)), ?_⟩
      rw [hφmul, hφinv, hφφ e heE, mul_inv_rev, inv_inv]
    · intro h
      exact hne' (mul_inv_eq_one.1 h).symm
  have horder : orderOf a = 3 := orderOf_eq_prime (hE3 a haE) ha1
  have hStab : ∀ s ∈ S, t * s * t⁻¹ ∈ S := by
    intro s hs
    obtain ⟨hsE, hs'⟩ := (hS s).1 hs
    refine (hS _).2 ⟨htE s hsE, ?_⟩
    rw [hφt, hs']
    group
  have hZS : zpowers a ≤ S := zpowers_le.2 haS
  have hZcard : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, horder]
  have hcardS : Nat.card S = 3 ∨ Nat.card S = 9 := by
    have hdvd : Nat.card S ∣ 9 := hE ▸ Subgroup.card_dvd_of_le hSE
    have h3 : 3 ∣ Nat.card S := hZcard ▸ Subgroup.card_dvd_of_le hZS
    have hle : Nat.card S ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card S = n at hdvd h3 hle ⊢
    interval_cases n <;> omega
  rcases hcardS with h3 | h9
  ·
    exfalso
    have hZ : zpowers a = S := Subgroup.eq_of_le_of_card_ge hZS (by rw [h3, hZcard])
    have hmem : t * a * t⁻¹ ∈ zpowers a := hZ ▸ hStab a haS
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    have hk3 : ¬ (3 : ℤ) ∣ k := by
      intro hdvd
      have h1 : a ^ k = 1 :=
        orderOf_dvd_iff_zpow_eq_one.1 (by rw [horder]; exact_mod_cast hdvd)
      rw [hk] at h1
      exact ha1 (by simpa using h1)
    have hkk : k * k % 3 = 1 := by
      have : k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases this with h | h <;> simp [Int.mul_emod, h]
    have hmod : a ^ (k * k % 3) = a ^ (k * k) := by
      have := zpow_mod_orderOf a (k * k)
      rwa [horder, Nat.cast_ofNat] at this
    have hconj : t * (t * a * t⁻¹) * t⁻¹ = a := by
      calc t * (t * a * t⁻¹) * t⁻¹ = t * a ^ k * t⁻¹ := by rw [hk]
        _ = (t * a * t⁻¹) ^ k := conj_zpow.symm
        _ = (a ^ k) ^ k := by rw [hk]
        _ = a ^ (k * k) := (zpow_mul a k k).symm
        _ = a := by rw [← hmod, hkk, zpow_one]
    have hφa : φ a = a := by
      have h' : φ a = t * (t * a * t⁻¹) * t⁻¹ := by rw [hφ, sq]; group
      rw [h', hconj]
    have hinv := ((hS a).1 haS).2
    rw [hφa] at hinv
    have hsq : a * a = 1 := mul_eq_one_iff_eq_inv.2 hinv
    apply ha1
    calc a = a ^ 3 * (a * a)⁻¹ := by group
      _ = 1 := by rw [hE3 a haE, hsq]; group
  ·
    have hSEq : S = E := Subgroup.eq_of_le_of_card_ge hSE (by rw [h9, hE])
    intro x hx
    have hxS : x ∈ S := hSEq ▸ hx
    have hx' := ((hS x).1 hxS).2
    rwa [hφ] at hx'

end CFSG.LocalAnalysis.RankThreeTheoremC

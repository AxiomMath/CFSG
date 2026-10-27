module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e4a0
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private def q13eFix (K H : Subgroup G) (f : G)
    (hH : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) : Subgroup G where
  carrier := {k | k ∈ K ∧ f * k * f⁻¹ * k⁻¹ ∈ H}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨haK, haH⟩ := ha
    obtain ⟨hbK, hbH⟩ := hb
    refine ⟨K.mul_mem haK hbK, ?_⟩
    have hid : f * (a * b) * f⁻¹ * (a * b)⁻¹
        = (f * a * f⁻¹ * a⁻¹) * (a * (f * b * f⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [hid]
    exact H.mul_mem haH (hH a haK _ hbH)
  one_mem' := by
    refine ⟨K.one_mem, ?_⟩
    have h1 : f * 1 * f⁻¹ * 1⁻¹ = 1 := by group
    rw [h1]
    exact H.one_mem
  inv_mem' := by
    intro a ha
    obtain ⟨haK, haH⟩ := ha
    refine ⟨K.inv_mem haK, ?_⟩
    have hid : f * a⁻¹ * f⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (f * a * f⁻¹ * a⁻¹)⁻¹ * a := by group
    rw [hid]
    simpa using hH a⁻¹ (K.inv_mem haK) _ (H.inv_mem haH)

private lemma q13eFix_card (K H : Subgroup G) (f : G)
    (hH : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) :
    Nat.card (q13eFix K H f hH)
      = ({k | k ∈ K ∧ f * k * f⁻¹ * k⁻¹ ∈ H} : Set G).ncard := by
  show Nat.card (↥(q13eFix K H f hH : Set G)) = _
  rw [Nat.card_coe_set_eq]
  rfl

private lemma q13e_commutator_mem {K H : Subgroup G}
    (hH : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hsq : ∀ k ∈ K, k * k ∈ H)
    {x y : G} (hx : x ∈ K) (hy : y ∈ K) : x * y * x⁻¹ * y⁻¹ ∈ H := by
  have hx2 : (x * x)⁻¹ ∈ H := H.inv_mem (hsq x hx)
  have hy2 : (y * y)⁻¹ ∈ H := H.inv_mem (hsq y hy)
  have hconj : y⁻¹ * (x * x)⁻¹ * y ∈ H := by
    simpa using hH y⁻¹ (K.inv_mem hy) ((x * x)⁻¹) hx2
  have hprod : (x * y) * (x * y) ∈ H := hsq (x * y) (K.mul_mem hx hy)
  have hid : x * y * x⁻¹ * y⁻¹
      = ((x * y) * (x * y)) * (y⁻¹ * (x * x)⁻¹ * y) * (y * y)⁻¹ := by group
  rw [hid]
  exact H.mul_mem (H.mul_mem hprod hconj) hy2

private lemma q13e_psi_psi {f k : G} (hf : f * f = 1) :
    f * (f * k * f⁻¹ * k⁻¹) * f⁻¹ * (f * k * f⁻¹ * k⁻¹)⁻¹
      = (k * (f * k⁻¹ * f⁻¹)) * (k * (f * k⁻¹ * f⁻¹)) := by
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  have hA : (f * k * f⁻¹ * k⁻¹)⁻¹ = k * f * k⁻¹ * f⁻¹ := by group
  rw [hfinv] at hA ⊢
  rw [hA]
  calc f * (f * k * f * k⁻¹) * f * (k * f * k⁻¹ * f)
      = (f * f) * (k * f * k⁻¹ * f * k * f * k⁻¹ * f) := by group
    _ = k * f * k⁻¹ * f * k * f * k⁻¹ * f := by rw [hf, one_mul]
    _ = k * (f * k⁻¹ * f) * (k * (f * k⁻¹ * f)) := by group

private lemma q13e_psi_diff_mem {K H : Subgroup G} {f : G}
    (hH : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hsq : ∀ k ∈ K, k * k ∈ H)
    (hfK : ∀ k ∈ K, f * k * f⁻¹ ∈ K)
    {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) :
    (f * (k * k') * f⁻¹ * (k * k')⁻¹) *
      ((f * k * f⁻¹ * k⁻¹) * (f * k' * f⁻¹ * k'⁻¹))⁻¹ ∈ H := by
  have hψk'K : f * k' * f⁻¹ * k'⁻¹ ∈ K := K.mul_mem (hfK k' hk') (K.inv_mem hk')
  have hcomm : k * (f * k' * f⁻¹ * k'⁻¹) * k⁻¹ * (f * k' * f⁻¹ * k'⁻¹)⁻¹ ∈ H :=
    q13e_commutator_mem hH hsq hk hψk'K
  have hψkK : f * k * f⁻¹ * k⁻¹ ∈ K := K.mul_mem (hfK k hk) (K.inv_mem hk)
  have hconj : (f * k * f⁻¹ * k⁻¹) *
      ((k * (f * k' * f⁻¹ * k'⁻¹) * k⁻¹) * (f * k' * f⁻¹ * k'⁻¹)⁻¹) *
      (f * k * f⁻¹ * k⁻¹)⁻¹ ∈ H :=
    hH _ hψkK _ hcomm
  have hid : (f * (k * k') * f⁻¹ * (k * k')⁻¹) *
      ((f * k * f⁻¹ * k⁻¹) * (f * k' * f⁻¹ * k'⁻¹))⁻¹
      = (f * k * f⁻¹ * k⁻¹) *
        ((k * (f * k' * f⁻¹ * k'⁻¹) * k⁻¹) * (f * k' * f⁻¹ * k'⁻¹)⁻¹) *
        (f * k * f⁻¹ * k⁻¹)⁻¹ := by group
  rw [hid]
  exact hconj

theorem q13e_card_mul_le_ncard_fix_sq {K H : Subgroup G} {f : G} (hHK : H ≤ K)
    (hH : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hsq : ∀ k ∈ K, k * k ∈ H) (hf : f * f = 1)
    (hfK : ∀ k ∈ K, f * k * f⁻¹ ∈ K) (hfH : ∀ h ∈ H, f * h * f⁻¹ ∈ H) :
    Nat.card K * Nat.card H ≤ ({k | k ∈ K ∧ f * k * f⁻¹ * k⁻¹ ∈ H} : Set G).ncard ^ 2 := by
  let Fix : Subgroup G := q13eFix K H f hH
  have hFix_le : Fix ≤ K := fun x hx => hx.1
  have hH_le_Fix : H ≤ Fix := by
    intro h hh
    exact ⟨hHK hh, H.mul_mem (hfH h hh) (H.inv_mem hh)⟩
  have hFix_norm : ∀ p ∈ Fix, ∀ n ∈ H, p * n * p⁻¹ ∈ H :=
    fun p hp n hn => hH p hp.1 n hn
  have hφ_mem : ∀ k ∈ K, f * k * f⁻¹ * k⁻¹ ∈ Fix := by
    intro k hk
    refine ⟨K.mul_mem (hfK k hk) (K.inv_mem hk), ?_⟩
    have huK : k * (f * k⁻¹ * f⁻¹) ∈ K := K.mul_mem hk (hfK k⁻¹ (K.inv_mem hk))
    have hsq' : (k * (f * k⁻¹ * f⁻¹)) * (k * (f * k⁻¹ * f⁻¹)) ∈ H := hsq _ huK
    rwa [q13e_psi_psi hf]
  have hmul : ∀ k ∈ K, ∀ k' ∈ K,
      (f * (k * k') * f⁻¹ * (k * k')⁻¹) *
        ((f * k * f⁻¹ * k⁻¹) * (f * k' * f⁻¹ * k'⁻¹))⁻¹ ∈ H :=
    fun k hk k' hk' => q13e_psi_diff_mem hH hsq hfK hk hk'
  have hker : ∀ k ∈ K, (f * k * f⁻¹ * k⁻¹) ∈ H ↔ k ∈ Fix :=
    fun k hk => ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩
  have hmain := q13e_card_mul_le_of_hom_mod (K := K) (H := Fix) (P' := Fix) (N' := H)
    (φ := fun k => f * k * f⁻¹ * k⁻¹) hFix_le hH_le_Fix hFix_norm hφ_mem hmul hker
  have hcard : Nat.card Fix = ({k | k ∈ K ∧ f * k * f⁻¹ * k⁻¹ ∈ H} : Set G).ncard :=
    q13eFix_card K H f hH
  calc Nat.card K * Nat.card H
      ≤ Nat.card Fix * Nat.card Fix := hmain
    _ = ({k | k ∈ K ∧ f * k * f⁻¹ * k⁻¹ ∈ H} : Set G).ncard ^ 2 := by
        rw [hcard, pow_two]

theorem q13e_two_mul_card_mul_le_ncard_fix_sq {K H : Subgroup G} {f : G} (hHK : H ≤ K)
    (hH : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hsq : ∀ k ∈ K, k * k ∈ H) (hf : f * f = 1)
    (hfK : ∀ k ∈ K, f * k * f⁻¹ ∈ K) (hfH : ∀ h ∈ H, f * h * f⁻¹ ∈ H) {c : G} (hc : c ∈ K)
    (hcf : f * c * f⁻¹ * c⁻¹ ∈ H) (hcK : ∀ k ∈ K, (f * k * f⁻¹ * k⁻¹) * c⁻¹ ∉ H) :
    2 * (Nat.card K * Nat.card H) ≤ ({k | k ∈ K ∧ f * k * f⁻¹ * k⁻¹ ∈ H} : Set G).ncard ^ 2 := by
  let Fix : Subgroup G := q13eFix K H f hH
  have hFix_le : Fix ≤ K := fun x hx => hx.1
  have hH_le_Fix : H ≤ Fix := by
    intro h hh
    exact ⟨hHK hh, H.mul_mem (hfH h hh) (H.inv_mem hh)⟩
  have hFix_norm : ∀ p ∈ Fix, ∀ n ∈ H, p * n * p⁻¹ ∈ H :=
    fun p hp n hn => hH p hp.1 n hn
  have hφ_mem : ∀ k ∈ K, f * k * f⁻¹ * k⁻¹ ∈ Fix := by
    intro k hk
    refine ⟨K.mul_mem (hfK k hk) (K.inv_mem hk), ?_⟩
    have huK : k * (f * k⁻¹ * f⁻¹) ∈ K := K.mul_mem hk (hfK k⁻¹ (K.inv_mem hk))
    have hsq' : (k * (f * k⁻¹ * f⁻¹)) * (k * (f * k⁻¹ * f⁻¹)) ∈ H := hsq _ huK
    rwa [q13e_psi_psi hf]
  have hmul : ∀ k ∈ K, ∀ k' ∈ K,
      (f * (k * k') * f⁻¹ * (k * k')⁻¹) *
        ((f * k * f⁻¹ * k⁻¹) * (f * k' * f⁻¹ * k'⁻¹))⁻¹ ∈ H :=
    fun k hk k' hk' => q13e_psi_diff_mem hH hsq hfK hk hk'
  have hker : ∀ k ∈ K, (f * k * f⁻¹ * k⁻¹) ∈ H ↔ k ∈ Fix :=
    fun k hk => ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩
  have hc_fix : c ∈ Fix := ⟨hc, hcf⟩
  have hmain := q13e_two_mul_card_mul_le_of_hom_mod (K := K) (H := Fix) (P' := Fix) (N' := H)
    (φ := fun k => f * k * f⁻¹ * k⁻¹) hFix_le hH_le_Fix hFix_norm hφ_mem hmul hker hc_fix hcK
  have hcard : Nat.card Fix = ({k | k ∈ K ∧ f * k * f⁻¹ * k⁻¹ ∈ H} : Set G).ncard :=
    q13eFix_card K H f hH
  calc 2 * (Nat.card K * Nat.card H)
      ≤ Nat.card Fix * Nat.card Fix := hmain
    _ = ({k | k ∈ K ∧ f * k * f⁻¹ * k⁻¹ ∈ H} : Set G).ncard ^ 2 := by
        rw [hcard, pow_two]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

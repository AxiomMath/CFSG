module

public import CFSG.GH74.GLS.TwoThin.Count
public import CFSG.GH74.GLS.TwoThin.Pumpup

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {H : Type*} [Group H]

omit [Group H] in
theorem mem_conjSub_of_conj_mem {H : Type*} [Group H] {L : Subgroup H} {t m : H}
    (h : t * m * t⁻¹ ∈ L) : m ∈ conjSub t⁻¹ L := by
  rw [mem_conjSub_iff']
  simpa using h

omit [Group H] in
theorem conj_mem_of_mem_conjSub {H : Type*} [Group H] {L : Subgroup H} {t m : H}
    (h : m ∈ conjSub t⁻¹ L) : t * m * t⁻¹ ∈ L := by
  rw [mem_conjSub_iff'] at h
  simpa using h

theorem centralizes_of_swap {L : Subgroup H} {t w : H} (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥)
    (hL : ⁅L, L⁆ = L) (hwt : w * t = t * w) (hwL : ∀ l ∈ L, w * l * w⁻¹ ∈ L)
    (hwI : ∀ l : ↥L, w * swapDiag hAB l = swapDiag hAB l * w) :
    ∀ l ∈ L, w * l * w⁻¹ = l := by
  have hwt1 : w * t * w⁻¹ = t := by
    rw [hwt]
    group
  have hwt2 : w * t⁻¹ * w⁻¹ = t⁻¹ := by
    have : w * t⁻¹ * w⁻¹ = (w * t * w⁻¹)⁻¹ := by group
    rw [this, hwt1]
  refine eq_of_normalizes_of_central hL fun l hl => ?_
  have hl₁ : w * l * w⁻¹ ∈ L := hwL l hl
  obtain ⟨l₁, hl₁def⟩ : ∃ l₁, l₁ = w * l * w⁻¹ := ⟨_, rfl⟩
  rw [← hl₁def] at hl₁
  have hδ : l₁ * (t⁻¹ * l₁ * t) = l * (t⁻¹ * l * t) := by
    have h1 : w * (l * (t⁻¹ * l * t)) = (l * (t⁻¹ * l * t)) * w := hwI ⟨l, hl⟩
    have h2 : w * (l * (t⁻¹ * l * t)) * w⁻¹ = l₁ * (t⁻¹ * l₁ * t) := by
      rw [hl₁def]
      calc w * (l * (t⁻¹ * l * t)) * w⁻¹
          = (w * l * w⁻¹) * (w * t⁻¹ * w⁻¹) * (w * l * w⁻¹) * (w * t * w⁻¹) := by group
        _ = (w * l * w⁻¹) * t⁻¹ * (w * l * w⁻¹) * t := by rw [hwt1, hwt2]
        _ = (w * l * w⁻¹) * (t⁻¹ * (w * l * w⁻¹) * t) := by group
    rw [← h2, h1]
    group
  have hz : l⁻¹ * l₁ = (t⁻¹ * l * t) * (t⁻¹ * l₁ * t)⁻¹ := by
    calc l⁻¹ * l₁ = l⁻¹ * (l₁ * (t⁻¹ * l₁ * t)) * (t⁻¹ * l₁ * t)⁻¹ := by group
      _ = l⁻¹ * (l * (t⁻¹ * l * t)) * (t⁻¹ * l₁ * t)⁻¹ := by rw [hδ]
      _ = (t⁻¹ * l * t) * (t⁻¹ * l₁ * t)⁻¹ := by group
  have hzL' : l⁻¹ * l₁ ∈ conjSub t⁻¹ L := by
    apply mem_conjSub_of_conj_mem
    have : t * (l⁻¹ * l₁) * t⁻¹ = l * l₁⁻¹ := by
      rw [hz]
      group
    rw [this]
    exact mul_mem hl (inv_mem hl₁)
  refine ⟨l⁻¹ * l₁, mul_mem (inv_mem hl) hl₁, fun m hm => ?_, by rw [hl₁def]; group⟩
  exact (commute_of_commutator_conj_eq_bot hAB hm hzL').symm

theorem commute_of_mem_conjSub_of_centralizes_swap {L : Subgroup H} {t w : H}
    (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥) (hw : w ∈ conjSub t⁻¹ L)
    (hwI : ∀ l : ↥L, w * swapDiag hAB l = swapDiag hAB l * w) :
    ∀ m ∈ conjSub t⁻¹ L, w * m = m * w := by
  intro m hm
  have hml : t * m * t⁻¹ ∈ L := conj_mem_of_mem_conjSub hm
  have hδ : w * ((t * m * t⁻¹) * (t⁻¹ * (t * m * t⁻¹) * t)) =
      ((t * m * t⁻¹) * (t⁻¹ * (t * m * t⁻¹) * t)) * w := hwI ⟨t * m * t⁻¹, hml⟩
  have hwl : w * (t * m * t⁻¹) = (t * m * t⁻¹) * w :=
    (commute_of_commutator_conj_eq_bot hAB hml hw).symm
  have hsimp : t⁻¹ * (t * m * t⁻¹) * t = m := by group
  rw [hsimp] at hδ
  have h1 : (t * m * t⁻¹) * (w * m) = (t * m * t⁻¹) * (m * w) := by
    have e1 : (t * m * t⁻¹) * (w * m) = ((t * m * t⁻¹) * w) * m := (mul_assoc _ _ _).symm
    have e2 : ((t * m * t⁻¹) * w) * m = (w * (t * m * t⁻¹)) * m := by rw [← hwl]
    have e3 : (w * (t * m * t⁻¹)) * m = w * ((t * m * t⁻¹) * m) := mul_assoc _ _ _
    have e4 : ((t * m * t⁻¹) * m) * w = (t * m * t⁻¹) * (m * w) := mul_assoc _ _ _
    rw [e1, e2, e3, hδ, e4]
  exact mul_left_cancel h1


theorem card_le_two_mul_of_forall {P : Type*} [Group P] [Finite P] (S : Subgroup P)
    (h : ∀ p₁ p₂ : P, p₁ ∉ S → p₂ ∉ S → p₁⁻¹ * p₂ ∈ S) :
    Nat.card P ≤ 2 * Nat.card S := by
  classical
  by_cases hall : ∀ p : P, p ∈ S
  · have : Nat.card P = Nat.card S := by
      apply Nat.card_congr
      exact (Equiv.ofBijective (fun p : S => (p : P))
        ⟨Subtype.coe_injective, fun p => ⟨⟨p, hall p⟩, rfl⟩⟩).symm
    omega
  · push Not at hall
    obtain ⟨p₁, hp₁⟩ := hall
    let f : P → S × Bool := fun p =>
      if hp : p ∈ S then (⟨p, hp⟩, false) else (⟨p₁⁻¹ * p, h p₁ p hp₁ hp⟩, true)
    have hf : Function.Injective f := by
      intro a b hab
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [f, ha, hb] at hab
      · exact hab
      · exact hab
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at this
    simpa [mul_comm] using this


theorem eq_one_of_pow_two_pow_eq_one_of_odd {Z : Type*} [Group Z] {z : Z} {n : ℕ}
    (hz : z ^ (2 ^ n) = 1) (hodd : Odd (orderOf z)) : z = 1 := by
  have hd : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hz
  obtain ⟨k, -, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hk : k = 0 := by
    by_contra hk0
    rw [hk2] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (by rw [Nat.even_pow]; exact ⟨even_two, hk0⟩)
  rw [hk, pow_zero] at hk2
  exact orderOf_eq_one_iff.mp hk2

end CFSG.GH74.GLS.TwoThin

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.Sporadic.HeldB
open scoped commutatorElement

section Model


theorem eq_bot_or_eq_heP {N : Subgroup (Equiv.Perm (Fin 8330))} (hNP : N ≤ heP)
    (hn : ∀ p ∈ heP, ∀ n ∈ N, p * n * p⁻¹ ∈ N) : N = ⊥ ∨ N = heP := by
  have : IsSimpleGroup heP := heP_simple
  have hnorm : (N.subgroupOf heP).Normal := by
    constructor
    intro n hn' p
    simp only [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hn' ⊢
    exact hn p p.2 n hn'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf heP) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hNP hx⟩ : heP) ∈ N.subgroupOf heP := hx
    rw [h, mem_bot] at h1
    exact mem_bot.mpr (congrArg Subtype.val h1)
  · right
    refine le_antisymm hNP fun x hx => ?_
    have h1 : (⟨x, hx⟩ : heP) ∈ N.subgroupOf heP := h ▸ mem_top _
    exact h1

theorem eq_one_of_odd_normalized {B : Subgroup (Equiv.Perm (Fin 8330))} (hBR : B ≤ heAutGroup)
    (hBodd : Odd (Nat.card B)) (hn : ∀ p ∈ heP, ∀ b ∈ B, p * b * p⁻¹ ∈ B) :
    ∀ b ∈ B, b = 1 := by
  have hD : B ⊓ heP = ⊥ := by
    rcases eq_bot_or_eq_heP (N := B ⊓ heP) inf_le_right (fun p hp n hn' =>
        mem_inf.mpr ⟨hn p hp n (mem_inf.mp hn').1,
          mul_mem (mul_mem hp (mem_inf.mp hn').2) (inv_mem hp)⟩) with h | h
    · exact h
    · exfalso
      have h2 := card_dvd_of_le (h.symm.le.trans inf_le_left)
      rw [card_heP] at h2
      have h3 := hBodd.of_dvd_nat h2
      norm_num at h3
  intro b hb
  apply eq_one_of_centralizes_heP
  intro g hg
  have h1 : ⁅b, g⁆ ∈ B ⊓ heP := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def, show b * g * b⁻¹ * g⁻¹ = b * (g * b⁻¹ * g⁻¹) by group]
      exact mul_mem hb (hn g hg b⁻¹ (inv_mem hb))
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp (heAutGroup_le_normalizer (hBR hb)) g).mp hg)
        (inv_mem hg)
  rw [hD, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem false_of_commuting_cover {A₁ A₂ : Subgroup (Equiv.Perm (Fin 8330))}
    (h₁ : A₁ ≤ heAutGroup) (h₂ : A₂ ≤ heAutGroup) (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x)
    (hcov : ∀ p ∈ heP, ∃ x ∈ A₁, ∃ y ∈ A₂, p = y * x) {c : Equiv.Perm (Fin 8330)}
    (hc : c ∈ heAutGroup) (hc₁ : ∀ x ∈ A₁, c⁻¹ * x * c ∈ A₂)
    (hc₂ : ∀ y ∈ A₂, c * y * c⁻¹ ∈ A₁) : False := by
  have hn : ∀ p ∈ heP, ∀ b ∈ A₁ ⊓ heP, p * b * p⁻¹ ∈ A₁ ⊓ heP := by
    intro p hp b hb
    obtain ⟨hb₁, hbP⟩ := mem_inf.mp hb
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem hp hbP) (inv_mem hp)⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hcov p hp
    have hxb : x * b * x⁻¹ ∈ A₁ := mul_mem (mul_mem hx hb₁) (inv_mem hx)
    have hc' := hcomm _ hxb y hy
    rw [show y * x * b * (y * x)⁻¹ = y * (x * b * x⁻¹) * y⁻¹ by group, ← hc',
      mul_inv_cancel_right]
    exact hxb
  rcases eq_bot_or_eq_heP inf_le_right hn with hB | hB
  ·
    have hB₁ : ∀ x ∈ A₁, x ∈ heP → x = 1 := fun x hx hxP => by
      have h1 : x ∈ A₁ ⊓ heP := mem_inf.mpr ⟨hx, hxP⟩
      rwa [hB, mem_bot] at h1
    have hB₂ : ∀ y ∈ A₂, y ∈ heP → y = 1 := by
      intro y hy hyP
      have h1 : c * y * c⁻¹ = 1 :=
        hB₁ _ (hc₂ y hy) ((mem_normalizer_iff.mp (heAutGroup_le_normalizer hc) y).mp hyP)
      calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    have two : ∀ {A : Subgroup (Equiv.Perm (Fin 8330))}, A ≤ heAutGroup →
        (∀ x ∈ A, x ∈ heP → x = 1) → ∃ x₀, ∀ x ∈ A, x = 1 ∨ x = x₀ := by
      intro A hA hAP
      by_cases h : ∃ x₀ ∈ A, x₀ ≠ 1
      · obtain ⟨x₀, hx₀, hx₀1⟩ := h
        refine ⟨x₀, fun x hx => ?_⟩
        by_cases hx1 : x = 1
        · exact Or.inl hx1
        · right
          have hx₀P : x₀ ∉ heP := fun h => hx₀1 (hAP x₀ hx₀ h)
          have hxP : x ∉ heP := fun h => hx1 (hAP x hx h)
          have h1 := hAP _ (mul_mem (inv_mem hx₀) hx)
            (inv_mul_mem_heP (hA hx₀) (hA hx) hx₀P hxP)
          exact (inv_mul_eq_one.mp h1).symm
      · push Not at h
        exact ⟨1, fun x hx => Or.inl (h x hx)⟩
    obtain ⟨x₀, hx₀⟩ := two h₁ hB₁
    obtain ⟨y₀, hy₀⟩ := two h₂ hB₂
    have hsub : (heP : Set (Equiv.Perm (Fin 8330))) ⊆ {1, x₀, y₀, y₀ * x₀} := by
      intro p hp
      obtain ⟨x, hx, y, hy, rfl⟩ := hcov p hp
      rcases hx₀ x hx with rfl | rfl <;> rcases hy₀ y hy with rfl | rfl <;> simp
    have h4 : ({1, x₀, y₀, y₀ * x₀} : Set (Equiv.Perm (Fin 8330))).ncard ≤ 4 := by
      have e1 := Set.ncard_insert_le (1 : Equiv.Perm (Fin 8330)) {x₀, y₀, y₀ * x₀}
      have e2 := Set.ncard_insert_le x₀ ({y₀, y₀ * x₀} : Set (Equiv.Perm (Fin 8330)))
      have e3 := Set.ncard_insert_le y₀ ({y₀ * x₀} : Set (Equiv.Perm (Fin 8330)))
      rw [Set.ncard_singleton] at e3
      omega
    have hcard : Nat.card heP ≤ 4 :=
      calc Nat.card heP = (heP : Set (Equiv.Perm (Fin 8330))).ncard := Nat.card_coe_set_eq _
        _ ≤ ({1, x₀, y₀, y₀ * x₀} : Set (Equiv.Perm (Fin 8330))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 4 := h4
    rw [card_heP] at hcard
    omega
  ·
    have hPA : heP ≤ A₁ := hB.symm.le.trans inf_le_left
    have hA₂ : ∀ y ∈ A₂, y = 1 := fun y hy =>
      eq_one_of_centralizes_heP fun g hg => hcomm g (hPA hg) y hy
    have hP : heP = ⊥ := by
      rw [eq_bot_iff]
      intro p hp
      have h1 := hA₂ _ (hc₁ p (hPA hp))
      rw [mem_bot]
      calc p = c * (c⁻¹ * p * c) * c⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h := card_heP
    rw [hP, card_bot] at h
    norm_num at h

end Model

end CFSG.ComponentClassification.GrSLit.HeDiag

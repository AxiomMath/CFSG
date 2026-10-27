module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Count

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard

@[expose] def omega {Γ : Type} [Group Γ] (e : Γ) : Set Γ := {x | ∃ h : Γ, x = h * e * h⁻¹}

theorem e_mem_omega {Γ : Type} [Group Γ] (e : Γ) : e ∈ omega e := ⟨1, by simp⟩

theorem conj_mem_omega {Γ : Type} [Group Γ] {e x : Γ} (hx : x ∈ omega e) (c : Γ) :
    c * x * c⁻¹ ∈ omega e := by
  obtain ⟨h, rfl⟩ := hx
  exact ⟨c * h, by group⟩

theorem pow_modEq_cases : ∀ c : ℕ, c ≤ 12 → 2 ^ 12 ≡ 2 ^ c [MOD 23] → c = 1 ∨ c = 12 := by
  decide

theorem pow_modEq_one_cases : ∀ a : ℕ, a ≤ 11 → 2 ^ a ≡ 1 [MOD 23] → a = 0 ∨ a = 11 := by
  decide

theorem eq_of_card_eq_two {α : Type*} [One α] (hc : Nat.card α = 2) {a b : α} (ha : a ≠ 1)
    (hb : b ≠ 1) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : α)).1 hc
  exact (hy a ha).trans (hy b hb).symm

namespace Setting65

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ} (hS : Setting65 Γ E H₁ e)
include hS

theorem omega_subset_E : omega e ⊆ E := by
  rintro _ ⟨h, rfl⟩
  exact hS.normal.conj_mem e hS.mem h

theorem ncard_omega : (omega e).ncard = 24 := hS.orbit

theorem g_not_mem_E {g : Γ} (hg23 : g ^ 23 = 1) (hg1 : g ≠ 1) : g ∉ E := by
  intro hgE
  have hsq : g ^ 2 = 1 := by simpa [pow_two] using hS.sq_of_mem_E hgE
  apply hg1
  calc g = g ^ 23 := by
        rw [show 23 = 2 * 11 + 1 by norm_num, pow_succ, pow_mul, hsq, one_pow, one_mul]
    _ = 1 := hg23

theorem normalizes_E (g : Γ) : ∀ x ∈ E, g * x * g⁻¹ ∈ E :=
  fun x hx => hS.normal.conj_mem x hx g

section Finite

variable [Finite Γ]

theorem exists_g : ∃ g : Γ, g ∈ H₁ ∧ g ^ 23 = 1 ∧ g ≠ 1 := by
  have := hS.normal₁
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  have hdvd : 23 ∣ Nat.card (H₁ ⧸ E.subgroupOf H₁) := by
    rw [hS.card₁]
    norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 23 hdvd
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  have h23 : (QuotientGroup.mk (h ^ 23) : H₁ ⧸ E.subgroupOf H₁) = 1 := by
    rw [QuotientGroup.mk_pow, ← hx]
    exact pow_orderOf_eq_one _
  have h23' : (h : Γ) ^ 23 ∈ E := by
    have := (QuotientGroup.eq_one_iff (h ^ 23)).1 h23
    simpa [mem_subgroupOf] using this
  have h46 : (h : Γ) ^ 46 = 1 := by
    have := hS.sq_of_mem_E h23'
    rw [← pow_add] at this
    simpa using this
  refine ⟨(h : Γ) ^ 2, H₁.pow_mem h.2 2, by rw [← pow_mul]; exact h46, fun h1 => ?_⟩
  have hh2 : h ^ 2 = 1 := Subtype.ext (by simpa using h1)
  have h2 : (QuotientGroup.mk h : H₁ ⧸ E.subgroupOf H₁) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hh2, QuotientGroup.mk_one]
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hx] at this
  norm_num at this

theorem card_E_inf_centralizer_g {g : Γ} (hg23 : g ^ 23 = 1) (hg1 : g ≠ 1) :
    Nat.card ↥(E ⊓ centralizer ({g} : Set Γ)) = 2 := by
  have hmod := card_modEq_card_inf_centralizer hg23 (E := E) (hS.normalizes_E g)
  have hdvd : Nat.card ↥(E ⊓ centralizer ({g} : Set Γ)) ∣ 2 ^ 12 := by
    rw [← hS.card]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨c, hc, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hcard, hS.card] at hmod
  rcases pow_modEq_cases c hc hmod with h1 | h12
  · rw [hcard, h1]
    norm_num
  · exfalso
    have hEq : E ⊓ centralizer ({g} : Set Γ) = E := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hcard, h12, hS.card]
    have hgC : g ∈ centralizer (E : Set Γ) := by
      rw [mem_centralizer_iff]
      intro x hx
      have hxE : x ∈ E ⊓ centralizer ({g} : Set Γ) := by
        rw [hEq]
        exact hx
      exact mem_centralizer_singleton_iff.1 hxE.2
    rw [hS.cent] at hgC
    exact hS.g_not_mem_E hg23 hg1 hgC

theorem E₁_inf_centralizer_g {g : Γ} (hgH : g ∈ H₁) (hg23 : g ^ 23 = 1) (hg1 : g ≠ 1) :
    E ⊓ H₁ ⊓ centralizer ({g} : Set Γ) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxE : x ∈ E ⊓ centralizer ({g} : Set Γ) := ⟨hx.1.1, hx.2⟩
  have heE : e ∈ E ⊓ centralizer ({g} : Set Γ) :=
    ⟨hS.mem, mem_centralizer_singleton_iff.2 (hS.commute_of_mem_H₁ hgH).symm⟩
  by_contra hx1
  have hx1' : (⟨x, hxE⟩ : ↥(E ⊓ centralizer ({g} : Set Γ))) ≠ 1 := fun h =>
    hx1 (by simpa using congrArg Subtype.val h)
  have he1' : (⟨e, heE⟩ : ↥(E ⊓ centralizer ({g} : Set Γ))) ≠ 1 := fun h =>
    hS.e_ne_one (by simpa using congrArg Subtype.val h)
  have hxe : x = e := congrArg Subtype.val
    (eq_of_card_eq_two (hS.card_E_inf_centralizer_g hg23 hg1) hx1' he1')
  exact hS.e_not_mem_H₁ (hxe ▸ hx.1.2)

theorem eq_E₁_of_invariant {g : Γ} (hgH : g ∈ H₁) (hg23 : g ^ 23 = 1) (hg1 : g ≠ 1)
    {D : Subgroup Γ} (hD : D ≤ E ⊓ H₁) (hgD : ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hD1 : D ≠ ⊥) :
    D = E ⊓ H₁ := by
  have hmod := card_modEq_card_inf_centralizer hg23 (E := D) hgD
  have hbot : D ⊓ centralizer ({g} : Set Γ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ E ⊓ H₁ ⊓ centralizer ({g} : Set Γ) := ⟨hD hx.1, hx.2⟩
    rw [hS.E₁_inf_centralizer_g hgH hg23 hg1] at hx'
    exact hx'
  rw [hbot, Subgroup.card_bot] at hmod
  have hdvd : Nat.card D ∣ 2 ^ 11 := by
    rw [← hS.card_E₁]
    exact Subgroup.card_dvd_of_le hD
  obtain ⟨a, ha, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hcard] at hmod
  rcases pow_modEq_one_cases a ha hmod with h0 | h11
  · exfalso
    apply hD1
    rw [← Subgroup.card_eq_one, hcard, h0]
    norm_num
  · exact Subgroup.eq_of_le_of_card_ge hD (by rw [hcard, h11, hS.card_E₁])

end Finite

end Setting65

end CFSG.EvenSporadicStandard.Induction.Balance

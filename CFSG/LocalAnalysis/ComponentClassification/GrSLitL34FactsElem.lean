module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {g x : G} (hg : g * g = 1) (hx : x ∈ zpowers g) :
    x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hg2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, hg2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, hg2, one_zpow, one_mul, zpow_one]

theorem card_zpowers_of_involution {g : G} (hg : g * g = 1) (hg1 : g ≠ 1) :
    Nat.card (zpowers g) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hg) hg1

theorem card_zpowers_sup_eq [Finite G] {x : G} (hx : x * x = 1) {H : Subgroup G}
    (hxH : x ∈ normalizer (H : Set G)) (hxn : x ∉ H) :
    Nat.card ↥(zpowers x ⊔ H) = 2 * Nat.card H := by
  refine le_antisymm (card_zpowers_sup_le hx hxH) ?_
  obtain ⟨m, hm⟩ := card_dvd_of_le (le_sup_right : H ≤ zpowers x ⊔ H)
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    interval_cases m
    · rw [mul_zero] at hm
      exact absurd hm (Nat.card_pos).ne'
    · rw [mul_one] at hm
      have heq : H = zpowers x ⊔ H :=
        eq_of_le_of_card_ge le_sup_right (by rw [hm])
      exact hxn (heq ▸ mem_sup_left (mem_zpowers x))
  rw [hm]
  calc 2 * Nat.card H ≤ m * Nat.card H := Nat.mul_le_mul_right _ hm2
    _ = Nat.card H * m := mul_comm _ _

theorem commute_zpowers_zpowers {a b : G} (hab : a * b = b * a) :
    ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
  exact ((Commute.zpow_zpow (show Commute a b from hab) i j)).eq

theorem mem_normalizer_of_commute {x : G} {H : Subgroup G} (h : ∀ y ∈ H, x * y = y * x) :
    x ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rwa [h y hy, mul_inv_cancel_right]
  · intro hy
    have h1 := h _ hy
    have e : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * ((x * y * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [h1]
        _ = x * y * x⁻¹ := by group
    rw [e]
    exact hy

theorem isEightGroup_of_three [Finite G] {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha1 : a ≠ 1) (hb' : b ∉ zpowers a) (hc' : c ∉ zpowers b ⊔ zpowers a) :
    IsEightGroup (zpowers c ⊔ (zpowers b ⊔ zpowers a)) := by
  have hcomm_ba : ∀ x ∈ zpowers b, ∀ y ∈ zpowers a, x * y = y * x :=
    commute_zpowers_zpowers hab.symm
  have hcomm_c : ∀ x ∈ zpowers c, ∀ y ∈ zpowers b ⊔ zpowers a, x * y = y * x := by
    refine commute_sup_right ?_ ?_
    · exact commute_zpowers_zpowers hbc.symm
    · exact commute_zpowers_zpowers hac.symm
  have hE2 : IsElemTwo (zpowers b ⊔ zpowers a) :=
    (isElemTwo_zpowers hb).sup (isElemTwo_zpowers ha) hcomm_ba
  refine ⟨(isElemTwo_zpowers hc).sup hE2 hcomm_c, ?_⟩
  have hca : c ∈ normalizer ((zpowers b ⊔ zpowers a : Subgroup G) : Set G) :=
    mem_normalizer_of_commute fun y hy => hcomm_c c (mem_zpowers c) y hy
  have hba : b ∈ normalizer ((zpowers a : Subgroup G) : Set G) :=
    mem_normalizer_of_commute fun y hy => hcomm_ba b (mem_zpowers b) y hy
  rw [card_zpowers_sup_eq hc hca hc', card_zpowers_sup_eq hb hba hb',
    card_zpowers_of_involution ha ha1]

end CFSG.ComponentClassification.GrSLit.L34Facts

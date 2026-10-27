module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSevenPerm

public section

namespace CFSG.ComponentClassification.HSFLit

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {g x : G} (hg : g ^ 2 = 1) (hx : x ∈ zpowers g) :
    x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ← sq, hg, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, ← sq, hg, one_zpow, one_mul, zpow_one]

structure ElemAbelianTwo (V : Subgroup G) : Prop where
  comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  sq_eq_one : ∀ a ∈ V, a ^ 2 = 1

theorem ElemAbelianTwo.bot : ElemAbelianTwo (⊥ : Subgroup G) :=
  ⟨fun a ha b hb => by rw [mem_bot.mp ha, mem_bot.mp hb], fun a ha => by rw [mem_bot.mp ha]; simp⟩

theorem ElemAbelianTwo.sup_zpowers [Finite G] {V : Subgroup G} (hV : ElemAbelianTwo V) {g : G}
    (hg2 : g ^ 2 = 1) (hgV : g ∉ V) (hgc : ∀ a ∈ V, g * a = a * g) :
    ElemAbelianTwo (V ⊔ zpowers g) ∧ (∀ a ∈ V ⊔ zpowers g, a ∈ V ∨ a * g ∈ V) ∧
      Nat.card (V ⊔ zpowers g : Subgroup G) = 2 * Nat.card V := by
  have hN : zpowers g ≤ normalizer (V : Set G) := by
    rw [zpowers_le]
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro a ha
    exact (hgc a ha).symm
  have hmem : ∀ a ∈ V ⊔ zpowers g, ∃ v ∈ V, a = v ∨ a = v * g := by
    intro a ha
    have ha' : a ∈ (V : Set G) * (zpowers g : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left V _ hN]
      exact ha
    obtain ⟨v, hv, k, hk, rfl⟩ := ha'
    rcases eq_one_or_eq_of_mem_zpowers hg2 hk with rfl | rfl
    · exact ⟨v, hv, Or.inl (mul_one v)⟩
    · exact ⟨v, hv, Or.inr rfl⟩
  have hgg : g * g = 1 := by rw [← pow_two, hg2]
  refine ⟨⟨fun a ha b hb => ?_, fun a ha => ?_⟩, fun a ha => ?_, ?_⟩
  · obtain ⟨v, hv, hav⟩ := hmem a ha
    obtain ⟨w, hw, hbw⟩ := hmem b hb
    have hvw := hV.comm v hv w hw
    rcases hav with h1 | h1 <;> rcases hbw with h2 | h2 <;> rw [h1, h2]
    · exact hvw
    · calc v * (w * g) = w * v * g := by rw [← hvw, mul_assoc]
        _ = w * (g * v) := by rw [hgc v hv, mul_assoc]
        _ = w * g * v := by rw [mul_assoc]
    · calc v * g * w = v * (w * g) := by rw [mul_assoc, hgc w hw]
        _ = w * (v * g) := by rw [← mul_assoc, hvw, mul_assoc]
    · calc v * g * (w * g) = v * (g * w) * g := by simp only [mul_assoc]
        _ = v * (w * g) * g := by rw [hgc w hw]
        _ = w * (v * g) * g := by rw [← mul_assoc v w g, hvw, mul_assoc w v g]
        _ = w * (g * v) * g := by rw [hgc v hv]
        _ = w * g * (v * g) := by simp only [mul_assoc]
  · obtain ⟨v, hv, hav⟩ := hmem a ha
    rcases hav with h1 | h1 <;> rw [h1]
    · exact hV.sq_eq_one v hv
    · calc (v * g) ^ 2 = v * (g * v) * g := by rw [pow_two]; simp only [mul_assoc]
        _ = v * v * (g * g) := by rw [hgc v hv]; simp only [mul_assoc]
        _ = 1 := by rw [← pow_two, hV.sq_eq_one v hv, hgg, one_mul]
  · obtain ⟨v, hv, hav⟩ := hmem a ha
    rcases hav with h1 | h1 <;> rw [h1]
    · exact Or.inl hv
    · right
      rw [mul_assoc, hgg, mul_one]
      exact hv
  · have hdisj : V ⊓ zpowers g = ⊥ := by
      rw [eq_bot_iff]
      rintro a ⟨haV, hag⟩
      rcases eq_one_or_eq_of_mem_zpowers hg2 hag with rfl | rfl
      · exact one_mem _
      · exact absurd haV hgV
    have hg1 : g ≠ 1 := fun h => hgV (h ▸ one_mem V)
    rw [card_sup_eq_mul_of_le_normalizer hN hdisj, Nat.card_zpowers, orderOf_eq_prime hg2 hg1,
      mul_comm]

theorem mem_or_mul_mem_of_mem_sup_zpowers {P : Subgroup G} {u : G} (hu2 : u ^ 2 = 1)
    (hu : u ∈ normalizer (P : Set G)) {h : G} (hh : h ∈ P ⊔ zpowers u) : h ∈ P ∨ h * u ∈ P := by
  have hN : zpowers u ≤ normalizer (P : Set G) := zpowers_le.mpr hu
  have hh' : h ∈ (P : Set G) * (zpowers u : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left P _ hN]
    exact hh
  obtain ⟨p, hp, v, hv, hpv⟩ := hh'
  simp only at hpv
  subst hpv
  rcases eq_one_or_eq_of_mem_zpowers hu2 hv with rfl | rfl
  · left
    rw [mul_one]
    exact hp
  · right
    rw [mul_assoc, ← pow_two, hu2, mul_one]
    exact hp

theorem commute_of_index_eq_two {H : Subgroup G} (hH : H.index = 2) (hHc : H ≤ center G)
    (a b : G) : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : H.Normal := normal_of_index_eq_two hH
  have : IsCyclic (G ⧸ H) := isCyclic_of_prime_card (p := 2) (by rw [← index_eq_card, hH])
  have := (QuotientGroup.mk' H).isMulCommutative_of_isCyclic_of_ker_le_center
    (by rw [QuotientGroup.ker_mk']; exact hHc)
  exact this.is_comm.comm a b

end CFSG.ComponentClassification.HSFLit

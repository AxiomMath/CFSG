module

public import CFSG.ClassicalInvolution.Asc77.AscT7TZStar

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution.Asc77

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers' {c x : G} (hc : c * c = 1) (hx : x ∈ Subgroup.zpowers c) :
    x = 1 ∨ x = c := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hc
  rw [zpow_eq_zpow_emod n h2]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem three_le_twoRank_of_commuting_involutions {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hac : a * c = c * a) (hbc : b * c = c * b) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (hc1 : c ≠ 1)
    (hcA : c ∉ Subgroup.closure ({a, b} : Set G)) : 3 ≤ twoRank G := by
  set A : Subgroup G := Subgroup.closure ({a, b} : Set G) with hA
  set C : Subgroup G := Subgroup.zpowers c with hC
  have hA2 : IsElemAbelian2 A 2 := T7A.isElemAbelian2_closure_pair ha hb ha1 hb1 hne hab
  have hA4 : Nat.card A = 4 := by simpa using hA2.1
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc) hc1
  have hC2 : Nat.card C = 2 := by rw [hC, Nat.card_zpowers, hc2]
  have hAcent : ∀ y ∈ A, y * c = c * y := by
    intro y hy
    have h1 : A ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [hA, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hac
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hbc
    exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hy)
  have hCcomm : ∀ w ∈ C, ∀ y ∈ A, y * w = w * y := by
    intro w hw y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (show Commute y c from hAcent y hy) n)).eq
  have hCcent : C ≤ Subgroup.centralizer (A : Set G) := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr (hCcomm w hw)
  have hCN : C ≤ Subgroup.normalizer (A : Set G) :=
    hCcent.trans (Subgroup.centralizer_le_normalizer _)
  have hinf : A ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers' hc hx.2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd (h ▸ hx.1) hcA
  have hcard := T7A.card_sup_mul_card_inf hCN
  rw [hinf, Subgroup.card_bot, hA4, hC2] at hcard
  have hE8 : Nat.card ↥(C ⊔ A) = 2 ^ 3 := by omega
  have hw2 : ∀ w ∈ C, w * w = 1 := by
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_add, ← two_mul, zpow_mul]
    have : c ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hc
    rw [this, one_zpow]
  have hsq : ∀ x ∈ C ⊔ A, x * x = 1 := by
    intro x hx
    have hxe : (↑(C ⊔ A) : Set G) = (C : Set G) * (A : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right C A hCN
    have hx' : x ∈ (↑(C ⊔ A) : Set G) := hx
    rw [hxe] at hx'
    obtain ⟨w, hw, y, hy, rfl⟩ := hx'
    have hyw : y * w = w * y := hCcomm w hw y hy
    have hy2 : y * y = 1 := hA2.2 y hy
    calc w * y * (w * y) = w * (y * w) * y := by group
      _ = w * (w * y) * y := by rw [hyw]
      _ = (w * w) * (y * y) := by group
      _ = 1 := by rw [hw2 w hw, hy2, one_mul]
  have hE : IsElemAbelian 2 (C ⊔ A) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (T7T.comm_of_sq_eq_one hsq x.2 y.2)⟩⟩, fun x hx => ?_⟩
    rw [pow_two]
    exact hsq x hx
  exact CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary G (C ⊔ A) hE 3 hE8

end CFSG.ClassicalInvolution.Hat2A7S

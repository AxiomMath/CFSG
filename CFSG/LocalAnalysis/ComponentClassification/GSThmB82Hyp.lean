module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Set
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Statements

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Hyp52

variable {X : Type} [Group X] [Finite X]

structure L82Hyp (h : Hyp52 X) : Prop where
  setting : Sec8Setting X h
  card_P : Nat.card h.P ≠ 4
  NP_eq : h.T = h.B ⊔ zpowers h.a ∧ h.B ⊓ zpowers h.a = ⊥ ∧ ∀ b ∈ h.B, b * h.a = h.a * b
  C_eq : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a
  J_normal : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X)
  S_sylow_C : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
    (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X))

variable {h : Hyp52 X}

theorem two_le_card_B : 2 ≤ Nat.card h.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 h.B := (Six.isPGroup_S h).to_le (h.B_le.trans inf_le_left)
  obtain ⟨k, hk⟩ := hB2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact h.B_ne_bot (Subgroup.eq_bot_of_card_eq _ hk)
  rw [hk]
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hk0)

namespace L82Hyp

variable (H : L82Hyp h)
include H

theorem isSimpleGroup : IsSimpleGroup X := H.setting.1

theorem maximal : GSMaximalUnbalancingTriple h.a h.x h.J := H.setting.2.2.2.2.2.1

theorem iso : GSIsoAt h.a h.J := H.setting.2.2.2.2.2.2.2.1

theorem eight_le_card_P : 8 ≤ Nat.card h.P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 h.P := (Six.isPGroup_S h).to_le inf_le_left
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hT : Nat.card h.T = 2 * Nat.card h.B := h.card_T H.NP_eq
  have hTP : Nat.card h.T ≤ Nat.card h.P := Subgroup.card_le_of_le inf_le_right
  have h4 : 4 ≤ Nat.card h.P := by
    have := h.two_le_card_B
    omega
  rw [hk] at h4 ⊢
  have hne : 2 ^ k ≠ 4 := by
    rw [← hk]
    exact H.card_P
  have hk3 : 3 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k <;> simp_all
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3

theorem not_P_le_normalizer_B : ¬ h.P ≤ normalizer (h.B : Set X) := by
  intro hPN
  rcases h.two_le_card_B.eq_or_lt with h2 | h2
  · have hTP : h.T = h.P := le_antisymm inf_le_right
      (le_inf (le_inf inf_le_left hPN) le_rfl)
    have hT := h.card_T H.NP_eq
    rw [hTP, ← h2] at hT
    exact H.card_P hT
  · exact h.not_P_le_normalizer H.NP_eq h2 hPN

theorem exists_prop62 (hS : SchreierFor Blueprint.Catalog) :
    ∃ y : X, h.IsX0Min y ∧ ∃ h' : Hyp52 X, Seven.Prop62Output h h' y := by
  have := H.isSimpleGroup
  obtain ⟨y, hy⟩ := h.exists_isX0Min H.not_P_le_normalizer_B
  refine ⟨y, hy, ?_⟩
  obtain ⟨-, hnonab, hK, -⟩ := H.setting
  exact prop62 hS hnonab hK h H.maximal H.iso H.NP_eq.1 H.C_eq
    ((normal_subgroupOf_iff_le_normalizer h.J_le).mpr H.J_normal) H.S_sylow_C
    H.not_P_le_normalizer_B hy

end L82Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB

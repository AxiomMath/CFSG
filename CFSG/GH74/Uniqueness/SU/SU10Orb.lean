module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem eq_of_odd_card {A : Subgroup X} {w y : X} {m : ℕ} (hm : 1 ≤ m)
    (hcard : Nat.card A = 2 ^ (m + 1)) (hwA : w ∈ A) (hw1 : w ≠ 1) (hww : w * w = 1)
    (hyw : y * w = w * y)
    (htrans : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → a ≠ w → b ≠ 1 → b ≠ w →
      ∃ j : ℤ, y ^ j * a * (y ^ j)⁻¹ = b ∨ y ^ j * a * (y ^ j)⁻¹ = b * w)
    (W : Set X) (hWA : W ⊆ (A : Set X)) (hW1 : (1 : X) ∉ W) (hwW : w ∈ W)
    (hWne : ∃ u ∈ W, u ≠ w) (hWy : ∀ a ∈ W, ∀ j : ℤ, y ^ j * a * (y ^ j)⁻¹ ∈ W)
    (hWodd : Odd W.ncard) : ∀ a ∈ A, a ≠ 1 → a ∈ W := by
  classical
  set U : Set X := {b | b ∈ A ∧ b ≠ 1 ∧ b ≠ w} with hU
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hcomm : ∀ j : ℤ, y ^ j * w * (y ^ j)⁻¹ = w := fun j => by
    have hc : Commute (y ^ j) w := (show Commute y w from hyw).zpow_left j
    rw [hc.eq, mul_inv_cancel_right]
  have hconjw : ∀ (j : ℤ) (a : X), y ^ j * (a * w) * (y ^ j)⁻¹ = (y ^ j * a * (y ^ j)⁻¹) * w := by
    intro j a
    calc y ^ j * (a * w) * (y ^ j)⁻¹ = y ^ j * a * (y ^ j)⁻¹ * (y ^ j * w * (y ^ j)⁻¹) := by group
      _ = (y ^ j * a * (y ^ j)⁻¹) * w := by rw [hcomm]
  obtain ⟨u, huW, hune⟩ := hWne
  have huU : u ∈ U := ⟨hWA huW, fun h => hW1 (h ▸ huW), hune⟩
  have hpair : ∀ b ∈ U, b ∈ W ∨ b * w ∈ W := by
    intro b hb
    obtain ⟨j, hj⟩ := htrans u huU.1 b hb.1 huU.2.1 huU.2.2 hb.2.1 hb.2.2
    rcases hj with hj | hj
    · exact Or.inl (hj ▸ hWy u huW j)
    · exact Or.inr (hj ▸ hWy u huW j)
  by_cases hall : ∀ b ∈ U, b ∈ W ∧ b * w ∈ W
  · intro a ha ha1
    by_cases haw : a = w
    · rw [haw]; exact hwW
    · exact (hall a ⟨ha, ha1, haw⟩).1
  · exfalso
    push Not at hall
    obtain ⟨b₀, hb₀U, hb₀⟩ := hall
    have hone : ∀ b ∈ U, ¬ (b ∈ W ∧ b * w ∈ W) := by
      rintro b hb ⟨hbW, hbwW⟩
      obtain ⟨j, hj⟩ := htrans b hb.1 b₀ hb₀U.1 hb.2.1 hb.2.2 hb₀U.2.1 hb₀U.2.2
      have h1 := hWy b hbW j
      have h2 := hWy (b * w) hbwW j
      rw [hconjw] at h2
      rcases hj with hj | hj
      · rw [hj] at h1 h2
        exact (hb₀ h1) h2
      · rw [hj] at h1 h2
        have h3 : b₀ * w * w ∈ W := h2
        rw [mul_assoc, hww, mul_one] at h3
        exact (hb₀ h3) h1
    set W₁ : Set X := W ∩ U with hW₁
    have hτU : ∀ b ∈ U, b * w ∈ U := by
      rintro b ⟨hbA, hb1, hbw⟩
      refine ⟨A.mul_mem hbA hwA, fun h => hbw ?_, fun h => hb1 ?_⟩
      · exact (mul_eq_one_iff_eq_inv.mp h).trans hwi
      · exact mul_right_cancel (h.trans (one_mul w).symm)
    have hdisj : Disjoint W₁ ((· * w) '' W₁) := by
      rw [Set.disjoint_left]
      rintro b ⟨hbW, hbU⟩ ⟨c, ⟨hcW, hcU⟩, hcb⟩
      apply hone c hcU
      refine ⟨hcW, ?_⟩
      have hcb' : c * w = b := hcb
      rw [hcb']
      exact hbW
    have hunion : U = W₁ ∪ ((· * w) '' W₁) := by
      ext b
      constructor
      · intro hb
        rcases hpair b hb with h | h
        · exact Or.inl ⟨h, hb⟩
        · refine Or.inr ⟨b * w, ⟨h, hτU b hb⟩, ?_⟩
          simp only
          rw [mul_assoc, hww, mul_one]
      · rintro (⟨-, hb⟩ | ⟨c, ⟨-, hc⟩, rfl⟩)
        · exact hb
        · exact hτU c hc
    have hinj : Function.Injective (· * w : X → X) := fun a b h => mul_right_cancel h
    have hcardU : U.ncard = 2 * W₁.ncard := by
      rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
        Set.ncard_image_of_injective _ hinj]
      ring
    have hAcard : (A : Set X).ncard = 2 ^ (m + 1) := by
      rw [← hcard]
      exact (Nat.card_coe_set_eq (A : Set X)).symm
    have hUeq : U = (A : Set X) \ {1, w} := by
      ext b
      simp only [hU, Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto
    have h1w : ({1, w} : Set X) ⊆ (A : Set X) := by
      intro b hb
      rcases hb with rfl | rfl
      · exact A.one_mem
      · exact hwA
    have hcard2 : ({1, w} : Set X).ncard = 2 := by
      rw [Set.ncard_pair (Ne.symm hw1)]
    have hcardU2 : U.ncard = 2 ^ (m + 1) - 2 := by
      rw [hUeq, Set.ncard_sdiff h1w (Set.toFinite _), hAcard, hcard2]
    have hWeq : W = W₁ ∪ {w} := by
      ext b
      constructor
      · intro hb
        by_cases hbw : b = w
        · exact Or.inr hbw
        · exact Or.inl ⟨hb, hWA hb, fun h => hW1 (h ▸ hb), hbw⟩
      · rintro (⟨hb, -⟩ | rfl)
        · exact hb
        · exact hwW
    have hwW₁ : w ∉ W₁ := fun h => h.2.2.2 rfl
    have hcardW : W.ncard = W₁.ncard + 1 := by
      rw [hWeq, Set.ncard_union_eq (Set.disjoint_singleton_right.mpr hwW₁) (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton]
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have hpos : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hW₁card : W₁.ncard = 2 ^ m - 1 := by
      have := hcardU.symm.trans hcardU2
      rw [hpow] at this
      omega
    have hWc : W.ncard = 2 ^ m := by
      rw [hcardW, hW₁card]
      omega
    rw [hWc] at hWodd
    have : Even (2 ^ m) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact (Nat.not_even_iff_odd.mpr hWodd) this

end CFSG.GH74.Uniqueness.SU.SU10

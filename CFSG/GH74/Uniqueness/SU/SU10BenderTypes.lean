module

public import CFSG.GH74.Uniqueness.SU.SU10X
public import CFSG.GH74.Uniqueness.SU.SU10Cl
public import CFSG.GH74.Uniqueness.SU.SU10Syl

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem bender_types (T : Sylow 2 X) {K₁ : Subgroup X} [K₁.Normal]
    (hK : CFSG.BenderSuzuki.IsBenderGroup ↥K₁) {w : X} (hw2 : orderOf w = 2)
    (hwc : ∀ x : X, x * w = w * x) (hwT : w ∈ (T : Subgroup X))
    (hC : Open.pRank 2 (centralizer (K₁ : Set X)) = 1)
    (hle : Subgroup.closure {g : X | g ∈ (T : Subgroup X) ∧ g * g = 1} ≤
      K₁ ⊔ centralizer (K₁ : Set X)) :
    w ∉ K₁ ∧ (∀ t : X, t * t = 1 → t ∈ K₁ ∨ t * w ∈ K₁) ∧
      (∀ a b : X, a ∈ K₁ → b ∈ K₁ → orderOf a = 2 → orderOf b = 2 → ∃ c : X, c⁻¹ * a * c = b) ∧
      (∀ a b : X, a * w ∈ K₁ → b * w ∈ K₁ → orderOf a = 2 → orderOf b = 2 → a ≠ w → b ≠ w →
        ∃ c : X, c⁻¹ * a * c = b) := by
  obtain ⟨hKC, -, hinvT, -, -⟩ := bender_config T hK hw2 hwc hwT hC hle
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, sq] at this
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  have hwC : w ∈ centralizer (K₁ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    exact hwc h
  have hwK : w ∉ K₁ := fun hw => hw1 (by
    have : w ∈ K₁ ⊓ centralizer (K₁ : Set X) := Subgroup.mem_inf.mpr ⟨hw, hwC⟩
    rw [hKC] at this
    simpa using this)
  have hcj : ∀ (c a : X), c⁻¹ * (a * w) * c = (c⁻¹ * a * c) * w := by
    intro c a
    calc c⁻¹ * (a * w) * c = c⁻¹ * a * (w * c) := by group
      _ = c⁻¹ * a * (c * w) := by rw [hwc c]
      _ = (c⁻¹ * a * c) * w := by group
  refine ⟨hwK, ?_, ?_, ?_⟩
  ·
    intro t htt
    have hzp : IsPGroup 2 (zpowers t) := by
      by_cases ht1 : t = 1
      · rw [ht1, Subgroup.zpowers_one_eq_bot]
        exact IsPGroup.of_card (n := 0) (by simp)
      · have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
        exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; simp)
    obtain ⟨c, -, hc⟩ := exists_conj_le (isSylowIn_top T) (le_top : zpowers t ≤ ⊤) hzp
    have htc : c⁻¹ * t * c ∈ (T : Subgroup X) := by
      obtain ⟨p, hp, hpt⟩ := hc (Subgroup.mem_zpowers t)
      have h1 : c * p * c⁻¹ = t := hpt
      have h2 : c⁻¹ * t * c = p := by rw [← h1]; group
      rw [h2]
      exact hp
    have htt' : (c⁻¹ * t * c) * (c⁻¹ * t * c) = 1 := by
      calc (c⁻¹ * t * c) * (c⁻¹ * t * c) = c⁻¹ * (t * t) * c := by group
        _ = 1 := by rw [htt]; group
    rcases hinvT (c⁻¹ * t * c) htc htt' with h1 | h1
    · left
      have := (inferInstance : K₁.Normal).conj_mem _ h1 c
      have h3 : c * (c⁻¹ * t * c) * c⁻¹ = t := by group
      rwa [h3] at this
    · right
      have h2 := (inferInstance : K₁.Normal).conj_mem _ h1 c
      have h3 : c * (c⁻¹ * t * c * w) * c⁻¹ = t * w := by
        calc c * (c⁻¹ * t * c * w) * c⁻¹ = t * (c * w * c⁻¹) := by group
          _ = t * w := by rw [hwc c]; group
      rwa [h3] at h2
  · intro a b ha hb ha2 hb2
    obtain ⟨c, -, hc⟩ := exists_conj_of_involutions_bender hK ha hb ha2 hb2
    exact ⟨c, hc⟩
  · intro a b ha hb ha2 hb2 haw hbw
    have haa : a * a = 1 := by
      have := pow_orderOf_eq_one a
      rwa [ha2, sq] at this
    have hbb : b * b = 1 := by
      have := pow_orderOf_eq_one b
      rwa [hb2, sq] at this
    have hka : orderOf (a * w) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [sq]
        calc a * w * (a * w) = a * (w * a) * w := by group
          _ = a * (a * w) * w := by rw [← hwc a]
          _ = (a * a) * (w * w) := by group
          _ = 1 := by rw [haa, hww, one_mul]
      · intro h1
        apply haw
        calc a = a * w * w := by rw [mul_assoc, hww, mul_one]
          _ = w := by rw [h1, one_mul]
    have hkb : orderOf (b * w) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [sq]
        calc b * w * (b * w) = b * (w * b) * w := by group
          _ = b * (b * w) * w := by rw [← hwc b]
          _ = (b * b) * (w * w) := by group
          _ = 1 := by rw [hbb, hww, one_mul]
      · intro h1
        apply hbw
        calc b = b * w * w := by rw [mul_assoc, hww, mul_one]
          _ = w := by rw [h1, one_mul]
    obtain ⟨c, -, hc⟩ := exists_conj_of_involutions_bender hK ha hb hka hkb
    refine ⟨c, ?_⟩
    have h1 : c⁻¹ * (a * w) * c = b * w := hc
    rw [hcj c a] at h1
    exact mul_right_cancel h1

end CFSG.GH74.Uniqueness.SU.SU10

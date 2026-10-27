module

public import CFSG.CGT.Timmesfeld75.Sec4OneCommon

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G]

@[expose] def Sec6Case (T T₁ : Subgroup G) (n m : ℕ) : Prop :=
  Nat.card T = 4 ∨ NaturalSL T (hSub T (normIn T₁ T)) n m ∨
    (Nat.card T = 16 ∧ ∃ _ : (T.subgroupOf (hSub T (normIn T₁ T))).Normal,
      (IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
        IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)))))

structure Sec6Ctx (T T₁ : Subgroup G) (n m : ℕ) : Prop where
  hy : StepHyp T T₁
  hS : Sec3Global T
  hI : Sec3IsoGlobal T
  hq : Nat.card T / Nat.card (normIn T T₁) = 2 ^ m
  hT : Nat.card T = (2 ^ m) ^ n
  hcase : Sec6Case T T₁ n m

section Basic

variable {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.finite (h : Sec6Ctx T T₁ n m) : Finite G := h.hy.finite

theorem Sec6Ctx.sec3 (h : Sec6Ctx T T₁ n m) : Sec3 T T₁ := h.hy.pair.sec3 h.hS

theorem Sec6Ctx.mul_card_normIn (h : Sec6Ctx T T₁ n m) :
    2 ^ m * Nat.card (normIn T T₁) = Nat.card T := by
  have hdvd : Nat.card (normIn T T₁) ∣ Nat.card T := Subgroup.card_dvd_of_le (normIn_le T T₁)
  rw [← h.hq]
  exact Nat.div_mul_cancel hdvd

theorem Sec6Ctx.one_le (h : Sec6Ctx T T₁ n m) : 1 ≤ n := by
  by_contra hn
  have h0 : n = 0 := by omega
  have := h.hy.card
  rw [h.hT, h0, pow_zero] at this
  omega

theorem Sec6Ctx.card_normIn (h : Sec6Ctx T T₁ n m) :
    Nat.card (normIn T T₁) = (2 ^ m) ^ (n - 1) := by
  have h2 : 0 < 2 ^ m := pow_pos (by norm_num) m
  refine Nat.eq_of_mul_eq_mul_left h2 ?_
  rw [h.mul_card_normIn, h.hT]
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := h.one_le; omega⟩
  rw [hn', Nat.add_sub_cancel, pow_succ, mul_comm]

theorem Sec6Ctx.card_normIn_swap (h : Sec6Ctx T T₁ n m) :
    Nat.card (normIn T₁ T) = Nat.card (normIn T T₁) := by
  have := h.finite
  exact h.sec3.card_normIn_swap

theorem Sec6Ctx.card_eq_sixteen_iff (h : Sec6Ctx T T₁ n m) :
    (Nat.card T = 16 ∧ Nat.card (normIn T T₁) = 8) ↔ (n = 4 ∧ m = 1) := by
  constructor
  · rintro ⟨hT16, hL8⟩
    have h1 : 2 ^ (m * n) = 2 ^ 4 := by
      rw [pow_mul, ← h.hT, hT16]
      norm_num
    have h2 : 2 ^ (m * (n - 1)) = 2 ^ 3 := by
      rw [pow_mul, ← h.card_normIn, hL8]
      norm_num
    have h1' := Nat.pow_right_injective (le_refl 2) h1
    have h2' := Nat.pow_right_injective (le_refl 2) h2
    have hn := h.one_le
    obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [hn', Nat.add_sub_cancel] at h2'
    rw [hn'] at h1'
    have hm : m = 1 := by nlinarith
    subst hm
    refine ⟨by omega, rfl⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨by rw [h.hT]; norm_num, by rw [h.card_normIn]; norm_num⟩

end Basic

@[expose] def Sec62 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m →
    ∀ x ∈ normD T, x ∉ T →
      Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card ↥(normIn T T₁) →
        ∀ y ∈ classD T, ∀ t ∈ T, y = x * t → ∃ s ∈ T, y = s⁻¹ * x * s

@[expose] def Sec63 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m →
    ∀ x ∈ normD T, x ∉ T →
      Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card ↥(normIn T T₁) ∨
        (Nat.card T = 16 ∧ Nat.card ↥(normIn T T₁) = 8 ∧
          Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = 4)

@[expose] def Sec64Eight : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m →
    Nat.card T = 16 → Nat.card ↥(normIn T T₁) = 8 → ∀ x ∈ normD T, x ∉ T →
      Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = 4 → x ∈ hSub T (normIn T₁ T)

end CFSG.CGT.Timmesfeld75

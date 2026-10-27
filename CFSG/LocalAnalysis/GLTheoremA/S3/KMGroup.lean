module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KMBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S3.KM

open CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem zpow_mem_pair {z : G} (hzz : z * z = 1) (i : ℤ) : z ^ i = 1 ∨ z ^ i = z := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
  · left
    rw [zpow_mul, zpow_two, hzz, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hzz, one_zpow, one_mul, zpow_one]

theorem card_ge_of_lt {A₁ A₂ : Subgroup G} (h : A₁ < A₂) : 2 * Nat.card A₁ ≤ Nat.card A₂ := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le h.le
  have hpos : 0 < Nat.card A₁ := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have hm1 : m < 2 := by
    by_contra hm2
    push Not at hm2
    have : Nat.card A₁ * 2 ≤ Nat.card A₁ * m := Nat.mul_le_mul_left _ hm2
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card A₂ := Nat.card_pos
    omega
  have hm' : m = 1 := by omega
  rw [hm', mul_one] at hm
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hm.le)

theorem exists_pow_sq_mem {T : Subgroup G} (hT : IsPGroup 2 T) {z x : G} (hx : x ∈ T)
    (hx1 : x ≠ 1) (hxz : x ≠ z) :
    ∃ n : ℕ, x ^ n ≠ 1 ∧ x ^ n ≠ z ∧ ((x ^ n) ^ 2 = 1 ∨ (x ^ n) ^ 2 = z) := by
  classical
  have hex : ∃ m : ℕ, x ^ (2 ^ m) = 1 ∨ x ^ (2 ^ m) = z := by
    obtain ⟨k, hk⟩ := hT ⟨x, hx⟩
    exact ⟨k, Or.inl (by simpa using congrArg Subtype.val hk)⟩
  set m := Nat.find hex with hm
  have hspec : x ^ (2 ^ m) = 1 ∨ x ^ (2 ^ m) = z := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp only [pow_zero, pow_one] at hspec
    rcases hspec with h | h
    · exact hx1 h
    · exact hxz h
  have hmin : ∀ j < m, ¬ (x ^ (2 ^ j) = 1 ∨ x ^ (2 ^ j) = z) := fun j hj => Nat.find_min hex hj
  refine ⟨2 ^ (m - 1), ?_, ?_, ?_⟩
  · intro h1
    exact hmin (m - 1) (by omega) (Or.inl h1)
  · intro h1
    exact hmin (m - 1) (by omega) (Or.inr h1)
  · have : (x ^ 2 ^ (m - 1)) ^ 2 = x ^ 2 ^ m := by
      rw [← pow_mul, ← pow_succ]
      congr 2
      omega
    rw [this]
    exact hspec

theorem eq_bot_of_commutator_eq_self {K S : Subgroup G} (hK : IsPGroup 2 K) (hSK : S ≤ K)
    (h : ⁅S, K⁆ = S) : S = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent K := hK.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries K).1 hnil
  have hle : ∀ m : ℕ, S ≤ K.lowerCentralSeries m := by
    intro m
    induction m with
    | zero => exact hSK
    | succ m ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      calc S = ⁅S, K⁆ := h.symm
        _ ≤ ⁅K.lowerCentralSeries m, K⁆ := Subgroup.commutator_mono ih le_rfl
  exact le_bot_iff.1 (hn ▸ hle n)

theorem le_of_normalizer_le {T S : Subgroup G} (hT : IsPGroup 2 T) (hST : S ≤ T)
    (h : ∀ t ∈ T, t ∈ normalizer (S : Set G) → t ∈ S) : T ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent T := hT.isNilpotent
  by_contra hTS
  have hlt : S.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hTS ?_
    intro t ht
    have : (⟨t, ht⟩ : T) ∈ S.subgroupOf T := htop ▸ mem_top _
    exact this
  have hnc := normalizerCondition_of_isNilpotent (G := T) (S.subgroupOf T) hlt
  obtain ⟨x, hxN, hxS⟩ := SetLike.exists_of_lt hnc
  have hxn : (x : G) ∈ normalizer (S : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro s hs
    have hs' : (⟨s, hST hs⟩ : T) ∈ S.subgroupOf T := hs
    have := (mem_normalizer_iff.1 hxN ⟨s, hST hs⟩).1 hs'
    exact this
  exact hxS (h x x.2 hxn)

end CFSG.LocalAnalysis.GLTheoremA.S3.KM

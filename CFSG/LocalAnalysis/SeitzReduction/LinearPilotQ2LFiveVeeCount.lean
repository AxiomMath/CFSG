module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylData

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Count

variable {G : Type} [Group G]

theorem conj_mem_centralizer_of_mul_comm {z y : G} (h : z * y = y * z) {c : G}
    (hc : c * y = y * c) : z * c * z⁻¹ * y = y * (z * c * z⁻¹) := by
  have hz' : z⁻¹ * y = y * z⁻¹ := by
    calc z⁻¹ * y = z⁻¹ * (y * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * y) * z⁻¹ := by rw [h]
      _ = y * z⁻¹ := by group
  calc z * c * z⁻¹ * y = z * c * (z⁻¹ * y) := by group
    _ = z * c * (y * z⁻¹) := by rw [hz']
    _ = z * (c * y) * z⁻¹ := by group
    _ = z * (y * c) * z⁻¹ := by rw [hc]
    _ = (z * y) * c * z⁻¹ := by group
    _ = (y * z) * c * z⁻¹ := by rw [h]
    _ = y * (z * c * z⁻¹) := by group

theorem mem_normalizer_centralizer_of_mul_comm {x y : G} (h : x * y = y * x) :
    x ∈ normalizer (centralizer ({y} : Set G) : Set G) := by
  have hx' : x⁻¹ * y = y * x⁻¹ := by
    calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * y) * x⁻¹ := by rw [h]
      _ = y * x⁻¹ := by group
  rw [mem_normalizer_iff]
  intro c
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have h1 := conj_mem_centralizer_of_mul_comm h (c := c) hc
    exact h1
  · intro hc
    have h1 := conj_mem_centralizer_of_mul_comm hx' (c := x * c * x⁻¹)
      hc
    have h2 : x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c := by group
    rw [h2] at h1
    exact h1

theorem card_modEq_card_inf_centralizer {p : ℕ} [hp : Fact p.Prime] {V : Subgroup G} [Finite V]
    {x : G} (hxV : x ∈ normalizer (V : Set G)) (hx : x ^ p = 1) :
    Nat.card V ≡ Nat.card (V ⊓ centralizer ({x} : Set G) : Subgroup G) [MOD p] := by
  have hH : zpowers x ≤ normalizer (V : Set G) := (zpowers_le).2 hxV
  have hHp : IsPGroup p (zpowers x) := by
    have h1 : Nat.card (zpowers x) ∣ p := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hx
    rcases (Nat.dvd_prime hp.out).1 h1 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
  let _ : MulAction (zpowers x) V :=
    MulAction.compHom V (V.normalizerMonoidHom.comp (Subgroup.inclusion hH))
  have hsmul : ∀ (h : zpowers x) (v : V), ((h • v : V) : G) = (h : G) * v * (h : G)⁻¹ :=
    fun h v => rfl
  have h1 := hHp.card_modEq_card_fixedPoints (α := V)
  have h2 : Nat.card (MulAction.fixedPoints (zpowers x) V) =
      Nat.card (V ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1, mem_inf.2 ⟨v.1.2, mem_centralizer_singleton_iff.2 ?_⟩⟩
        invFun := fun v => ⟨⟨v.1, (mem_inf.1 v.2).1⟩, fun h => ?_⟩
        left_inv := fun v => rfl
        right_inv := fun v => rfl }
    · have h := congrArg Subtype.val (v.2 ⟨x, mem_zpowers x⟩)
      rw [hsmul] at h
      calc (v.1 : G) * x = x * v.1 * x⁻¹ * x := by rw [h]
        _ = x * v.1 := by group
    · obtain ⟨k, hk⟩ := h.2
      have hc : (h : G) ∈ centralizer ({(v : G)} : Set G) := by
        rw [← hk]
        exact Subgroup.zpow_mem _ (mem_centralizer_singleton_iff.2
          (mem_centralizer_singleton_iff.1 (mem_inf.1 v.2).2).symm) k
      apply Subtype.ext
      rw [hsmul]
      rw [mem_centralizer_singleton_iff] at hc
      change (h : G) * v * (h : G)⁻¹ = v
      rw [hc]
      group
  rwa [h2] at h1

theorem exists_card_eq_two_pow_of_le {V A : Subgroup G} (hV : Nat.card V = 16) (hAV : A ≤ V) :
    ∃ k ≤ 4, Nat.card A = 2 ^ k := by
  have h := Subgroup.card_dvd_of_le hAV
  rw [hV, show (16 : ℕ) = 2 ^ 4 by norm_num] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).1 h

theorem card_inf_centralizer_le_four_of_pow_three [Finite G] {V : Subgroup G} (hV : Nat.card V = 16)
    {x : G} (hxV : x ∈ normalizer (V : Set G)) (hx : x ^ 3 = 1)
    (hnt : ¬ V ≤ centralizer ({x} : Set G)) :
    Nat.card (V ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := card_modEq_card_inf_centralizer hxV hx
  obtain ⟨k, hk, hkc⟩ := exists_card_eq_two_pow_of_le hV (inf_le_left :
    V ⊓ centralizer ({x} : Set G) ≤ V)
  have hne : k ≠ 4 := by
    rintro rfl
    apply hnt
    have h := Subgroup.eq_of_le_of_card_ge (inf_le_left : V ⊓ centralizer ({x} : Set G) ≤ V)
      (by rw [hV, hkc]; norm_num)
    rw [← h]
    exact inf_le_right
  rw [hV, hkc] at hmod
  rw [hkc]
  interval_cases k <;> simp_all [Nat.ModEq]

theorem inf_centralizer_eq_bot_of_pow_fifteen [Finite G] {V : Subgroup G} (hV : Nat.card V = 16)
    {ζ : G} (hζV : ζ ∈ normalizer (V : Set G)) (hζ : ζ ^ 15 = 1)
    (hnt3 : ¬ V ≤ centralizer ({ζ ^ 3} : Set G)) (hnt5 : ¬ V ≤ centralizer ({ζ ^ 5} : Set G)) :
    V ⊓ centralizer ({ζ ^ 5} : Set G) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h35 : (ζ ^ 3) ^ 5 = 1 := by rw [← pow_mul]; exact hζ
  have hζ3V : ζ ^ 3 ∈ normalizer (V : Set G) := Subgroup.pow_mem _ hζV 3
  have hc3 : Nat.card (V ⊓ centralizer ({ζ ^ 3} : Set G) : Subgroup G) = 1 := by
    have hmod := card_modEq_card_inf_centralizer hζ3V h35
    obtain ⟨k, hk, hkc⟩ := exists_card_eq_two_pow_of_le hV (inf_le_left :
      V ⊓ centralizer ({ζ ^ 3} : Set G) ≤ V)
    have hne : k ≠ 4 := by
      rintro rfl
      apply hnt3
      have h := Subgroup.eq_of_le_of_card_ge (inf_le_left :
        V ⊓ centralizer ({ζ ^ 3} : Set G) ≤ V) (by rw [hV, hkc]; norm_num)
      rw [← h]
      exact inf_le_right
    rw [hV, hkc] at hmod
    rw [hkc]
    interval_cases k <;> simp_all [Nat.ModEq]
  set A := V ⊓ centralizer ({ζ ^ 5} : Set G) with hAdef
  have hcomm : ζ ^ 3 * ζ ^ 5 = ζ ^ 5 * ζ ^ 3 := by rw [← pow_add, ← pow_add, add_comm]
  have hζ3A : ζ ^ 3 ∈ normalizer (A : Set G) :=
    mem_normalizer_inf_of_mem_normalizer hζ3V (mem_normalizer_centralizer_of_mul_comm hcomm)
  have hmod := card_modEq_card_inf_centralizer hζ3A h35
  have hAA : Nat.card (A ⊓ centralizer ({ζ ^ 3} : Set G) : Subgroup G) = 1 := by
    have hle : A ⊓ centralizer ({ζ ^ 3} : Set G) ≤ V ⊓ centralizer ({ζ ^ 3} : Set G) :=
      inf_le_inf_right _ inf_le_left
    have h1 := Subgroup.card_le_of_le hle
    rw [hc3] at h1
    have h2 : 0 < Nat.card (A ⊓ centralizer ({ζ ^ 3} : Set G) : Subgroup G) := Nat.card_pos
    omega
  obtain ⟨k, hk, hkc⟩ := exists_card_eq_two_pow_of_le hV (inf_le_left : A ≤ V)
  have hne : k ≠ 4 := by
    rintro rfl
    apply hnt5
    have h := Subgroup.eq_of_le_of_card_ge (inf_le_left : A ≤ V) (by rw [hV, hkc]; norm_num)
    rw [← h]
    exact inf_le_right
  rw [hAA, hkc] at hmod
  have hA1 : Nat.card A = 1 := by
    rw [hkc]
    interval_cases k <;> simp_all [Nat.ModEq]
  exact Subgroup.card_eq_one.1 hA1

end Count

end CFSG.SeitzReduction.LinearPilot

module

public import CFSG.GroupTheory.SmallFixedTwoGroup.TheoremPFiveCentralizer

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup
open CFSG.ComponentClassification.LiteratureLocal.Order504

variable {G : Type*} [Group G]

private theorem five_arith {n r : ℕ} (hmod : n % 5 = 1) (hne : n ≠ 1) (hr : 2 ≤ r)
    (hbound : r * n ≤ 16) : n = 6 ∧ r = 2 := by
  have hdecomp : n % 5 + 5 * (n / 5) = n := Nat.mod_add_div n 5
  have hlin : 1 + 5 * (n / 5) = n := by rw [hmod] at hdecomp; exact hdecomp
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · simp at hmod
      · exact absurd rfl hne
    · exact h
  have hn8 : n ≤ 8 := by
    have h : 2 * n ≤ r * n := Nat.mul_le_mul_right n hr
    have := h.trans hbound
    omega
  have hn6 : n = 6 := by
    have hdiv_le : n / 5 ≤ 1 := by omega
    have hdiv_ge : 1 ≤ n / 5 := by omega
    omega
  subst hn6
  have hr2 : r ≤ 2 := by omega
  exact ⟨rfl, by omega⟩

theorem card_eq_sixty_of_sylow_five [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (h5 : 5 ∣ Nat.card G) (P : Sylow 5 G)
    (hab : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a)
    (hbound : (centralizer ((P : Subgroup G) : Set G)).index * (5 - 4) ≤ 4 * (5 - 1)) :
    Nat.card G = 60 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C : Subgroup G := centralizer ((P : Subgroup G) : Set G) with hC
  set N : Subgroup G := normalizer ((P : Subgroup G) : Set G) with hN
  have hPne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card h5
  have hPcard_ne_one : Nat.card (P : Subgroup G) ≠ 1 :=
    fun h => hPne (Subgroup.eq_bot_of_card_eq (P : Subgroup G) h)
  have hPtop : Nat.card (P : Subgroup G) ≠ Nat.card G := by
    intro h
    have htop : (P : Subgroup G) = ⊤ := Subgroup.eq_top_of_card_eq (P : Subgroup G) h
    rcases hnab with ⟨a, b, hab'⟩
    exact hab' (hab a (by rw [htop]; exact mem_top a) b (by rw [htop]; exact mem_top b))
  have hPn : ¬ (P : Subgroup G).Normal := not_normal_of_card hPcard_ne_one hPtop
  have hPleC : (P : Subgroup G) ≤ C := by
    rw [hC]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact (hab a ha b hb).symm
  have hCN : C ≤ N := by
    rw [hC, hN]
    exact centralizer_le_normalizer _
  have hCtop : C ≠ ⊤ := by
    intro hCtop
    apply hPn
    have hNtop : N = ⊤ := by
      have h : ⊤ ≤ N := hCtop ▸ hCN
      rw [hN] at h
      exact top_le_iff.mp h
    rw [← normalizer_eq_top_iff, ← hN]
    exact hNtop
  have hNC : ¬ N ≤ C := by
    intro h
    rw [hC, hN] at h
    exact false_of_normalizer_le_centralizer P h5 hPtop h
  set r : ℕ := C.relIndex N with hr
  have hrel : r * N.index = C.index := by
    rw [hr]
    exact Subgroup.relIndex_mul_index hCN
  have hNidx : N.index = Nat.card (Sylow 5 G) := by
    rw [hN]
    exact index_normalizer_sylow P
  have hm16 : C.index ≤ 16 := by
    simpa [hC] using hbound
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hrel
    rw [zero_mul] at hrel
    exact Subgroup.FiniteIndex.index_ne_zero hrel.symm
  have hr1 : r ≠ 1 := by
    intro h
    apply hNC
    rw [hr] at h
    exact Subgroup.relIndex_eq_one.mp h
  have hr2 : 2 ≤ r := by
    have hr0' : 0 < r := Nat.pos_of_ne_zero hr0
    have hr1' : 1 < r := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hr0, hr1⟩
    omega
  have hrmul : r * Nat.card (Sylow 5 G) ≤ 16 := by
    rw [← hNidx, hrel]
    exact hm16
  have hmod5 : Nat.card (Sylow 5 G) % 5 = 1 := by
    have h : Nat.ModEq 5 (Nat.card (Sylow 5 G)) 1 := card_sylow_modEq_one 5 G
    change Nat.card (Sylow 5 G) % 5 = 1 % 5 at h
    rw [Nat.mod_eq_of_lt (by norm_num : 1 < 5)] at h
    exact h
  have hn_ne_one : Nat.card (Sylow 5 G) ≠ 1 := by
    intro h
    haveI : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h).1
    exact hPn P.normal_of_subsingleton
  obtain ⟨hn6, hr2eq⟩ := five_arith hmod5 hn_ne_one hr2 hrmul
  have hGdvd : Nat.card G ∣ 720 := by
    have h := Subgroup.card_dvd_of_injective (MulAction.toPermHom G (Sylow 5 G))
      (toPermHom_sylow_injective P hPn)
    rw [Nat.card_perm, hn6] at h
    norm_num at h
    exact h
  have hPcard_dvd : Nat.card (P : Subgroup G) ∣ 720 :=
    (Subgroup.card_subgroup_dvd_card (P : Subgroup G)).trans hGdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have h5k_dvd : 5 ^ k ∣ 720 := by
    rw [← hk]
    exact hPcard_dvd
  have hk1 : k = 1 := by
    have hk_le : k ≤ 1 := by
      by_contra h
      have hk2 : 2 ≤ k := by omega
      have h25 : 5 ^ 2 ∣ 5 ^ k := pow_dvd_pow 5 hk2
      have hdvd : 5 ^ 2 ∣ 720 := h25.trans h5k_dvd
      have hno : ¬ (5 ^ 2 ∣ 720) := by
        intro hd
        have h' := Nat.dvd_iff_mod_eq_zero.mp hd
        norm_num at h'
      exact hno hdvd
    have hk_pos : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exfalso
        rw [h, pow_zero] at hk
        exact hPcard_ne_one hk
      · exact h
    omega
  have hP5 : Nat.card (P : Subgroup G) = 5 := by
    rw [hk, hk1, pow_one]
  have hCle5 : Nat.card C ≤ 5 := by
    rw [hC]
    exact card_centralizer_sylow_five_le P hP5 hn6
  have hCge5 : 5 ≤ Nat.card C := by
    have h := Subgroup.card_le_of_le hPleC
    rwa [hP5] at h
  have hCcard : Nat.card C = 5 := le_antisymm hCle5 hCge5
  have hCindex : C.index = 12 := by
    have h := hrel
    rw [hr2eq, hNidx, hn6] at h
    omega
  have hcard := Subgroup.index_mul_card C
  rw [hCindex, hCcard] at hcard
  norm_num at hcard
  exact hcard.symm

end CFSG.GroupTheory.SmallFixedTwoGroup

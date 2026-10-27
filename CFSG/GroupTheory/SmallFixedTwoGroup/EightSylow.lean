module

public import CFSG.GroupTheory.SmallFixedTwoGroup.PropB
public import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylowBurnside
public import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylowThree
public import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylowSevenMain
public import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylowAlt5

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

private lemma eq_one_or_three_or_seven_of_le_seven {m : ℕ} (hm0 : m ≠ 0) (hm2 : ¬ 2 ∣ m)
    (hm37 : ∀ r : ℕ, r.Prime → r ∣ m → r = 3 ∨ r = 7) (hle : m ≤ 7) :
    m = 1 ∨ m = 3 ∨ m = 7 := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  interval_cases m
  · exact Or.inl rfl
  · exfalso; exact hm2 (by norm_num)
  · exact Or.inr (Or.inl rfl)
  · exfalso; exact absurd (hm37 2 Nat.prime_two (by norm_num)) (by norm_num)
  · exfalso; exact absurd (hm37 5 (by decide) (by norm_num)) (by norm_num)
  · exfalso; exact hm2 (by norm_num)
  · exact Or.inr (Or.inr rfl)

theorem false_of_perfect_of_centralizer_eight_of_alt5 {E : Type*} [Group E] [Finite E]
    (hE : _root_.commutator E = ⊤) {t : E} (ht : orderOf t = 2)
    (hab : ∀ a ∈ centralizer ({t} : Set E), ∀ b ∈ centralizer ({t} : Set E), a * b = b * a)
    (hcard : Nat.card (centralizer ({t} : Set E)) = 8) (A : Subgroup E)
    (hA : Nonempty (A ≃* alternatingGroup (Fin 5))) : False := by
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  obtain ⟨P, hPC⟩ := exists_sylow_eq_centralizer_of_perfect hE ht hab hcard
  have hP_ab : ∀ a ∈ (P : Subgroup E), ∀ b ∈ (P : Subgroup E), a * b = b * a := by
    intro a ha b hb
    rw [hPC] at ha hb
    exact hab a ha b hb
  have hP_card : Nat.card (P : Subgroup E) = 8 := by rw [hPC]; exact hcard
  have ht_mem : t ∈ (P : Subgroup E) := by
    rw [hPC, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    rfl
  have hP_cent : ∀ x : E, (∀ y ∈ (P : Subgroup E), x * y = y * x) →
      x ∈ (P : Subgroup E) := by
    intro x hx
    rw [hPC, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (hx t ht_mem).symm
  have hC : centralizer ({t} : Set E) ≤ (P : Subgroup E) := le_of_eq hPC.symm
  set m : ℕ := (P : Subgroup E).relIndex (normalizer ((P : Subgroup E) : Set E)) with hm
  have hm_le7 : m ≤ 7 := by
    have h := relIndex_normalizer_le_card_sub_one ht_mem ht1 hC
    rw [hP_card] at h
    rw [← hm] at h
    omega
  have h2dvd : ¬ 2 ∣ m := by
    intro h2
    have hmdvd : m ∣ (P : Subgroup E).index := by
      rw [hm]
      exact Subgroup.relIndex_dvd_index_of_le (Subgroup.le_normalizer (H := (P : Subgroup E)))
    exact Sylow.not_dvd_index P (h2.trans hmdvd)
  have hm_ne0 : m ≠ 0 := by
    intro h0
    exact h2dvd (by rw [h0]; exact dvd_zero 2)
  have hprime37 : ∀ r : ℕ, r.Prime → r ∣ m → r = 3 ∨ r = 7 := by
    intro r hr hrdvd
    haveI : Fact r.Prime := ⟨hr⟩
    have hrdvd' : r ∣ (P : Subgroup E).relIndex
        (normalizer ((P : Subgroup E) : Set E)) := by
      rwa [← hm]
    obtain ⟨x, hxN, hxord⟩ :=
      exists_mem_normalizer_orderOf_eq_of_prime_dvd_relIndex (T := (P : Subgroup E)) hrdvd'
    have hr2 : r ≠ 2 := by
      intro h
      apply h2dvd
      rw [h] at hrdvd
      exact hrdvd
    have hxr : x ^ r = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    have hne : ¬ (P : Subgroup E) ≤ centralizer ({x} : Set E) := by
      intro hle
      have hxP : x ∈ (P : Subgroup E) := by
        apply hP_cent
        intro y hy
        have hy' : y ∈ centralizer ({x} : Set E) := hle hy
        rw [Subgroup.mem_centralizer_iff] at hy'
        exact hy' x (Set.mem_singleton x)
      have hdiv : orderOf x ∣ Nat.card (P : Subgroup E) :=
        Subgroup.orderOf_dvd_natCard (P : Subgroup E) hxP
      have hr8 : r ∣ 8 := by
        rw [hxord, hP_card] at hdiv
        exact hdiv
      have hpow : r ∣ 2 ^ 3 := by
        rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
        exact hr8
      have h2dvd' : r ∣ 2 := hr.dvd_of_dvd_pow hpow
      rcases (Nat.dvd_prime Nat.prime_two).mp h2dvd' with h | h
      · exact hr.ne_one h
      · exact hr2 h
    rcases prime_order_acts_on_order_eight (T := (P : Subgroup E)) hP_card hr2 hxr hxN hne with
      ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hm_cases : m = 1 ∨ m = 3 ∨ m = 7 :=
    eq_one_or_three_or_seven_of_le_seven hm_ne0 h2dvd hprime37 hm_le7
  rcases hm_cases with h1 | h3 | h7
  · exfalso
    have hrel1 : (P : Subgroup E).relIndex (normalizer ((P : Subgroup E) : Set E)) = 1 := by
      rw [← hm]; exact h1
    have hNP : normalizer ((P : Subgroup E) : Set E) ≤ (P : Subgroup E) :=
      Subgroup.relIndex_eq_one.mp hrel1
    have hPcP : (P : Subgroup E) ≤ centralizer ((P : Subgroup E) : Set E) := by
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact hP_ab q hq p hp
    have hcard1 : Nat.card (P : Subgroup E) = 1 :=
      card_eq_one_of_normalizer_le_centralizer hE P (le_trans hNP hPcP)
    rw [hP_card] at hcard1
    norm_num at hcard1
  · exact false_of_relIndex_normalizer_eq_three (index_ne_two_of_commutator_eq_top hE) P
      hP_ab hP_card hP_cent (by rw [← hm]; exact h3)
  · obtain ⟨a, x, ha, ha1, hx, hx1, hcomm⟩ := exists_involution_order_three_commute A hA
    exact false_of_relIndex_normalizer_eq_seven P hP_ab hP_card ht1 hPC.symm
      (by rw [← hm]; exact h7) ha ha1 hx hx1 hcomm

end CFSG.GroupTheory.SmallFixedTwoGroup

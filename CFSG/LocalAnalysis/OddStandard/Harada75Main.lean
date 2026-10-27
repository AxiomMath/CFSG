module

public import CFSG.LocalAnalysis.OddStandard.Harada75Suz
public import CFSG.LocalAnalysis.OddStandard.Harada75CaseII
public import CFSG.LocalAnalysis.OddStandard.Harada75CaseIa
public import CFSG.LocalAnalysis.OddStandard.Harada75CaseIc

public section

namespace CFSG.OddStandard.Harada75

open Subgroup
open scoped commutatorElement

variable {S : Type} [Group S]

theorem noE32_of_small [Finite S] {A E : Subgroup S} (h : Cfg S A E) (hS : Nat.card S ≤ 32) :
    NoE32 S := by
  rintro T U ⟨hUT, hsq, hcomm, hcard⟩
  have hTS : Nat.card T ≤ Nat.card S := Subgroup.card_le_card_group T
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hU1 : Nat.card U = 1 := by omega
  have hT32 : Nat.card T = 32 := by omega
  have hTtop : T = ⊤ := Subgroup.eq_top_of_card_eq T (by omega)
  have hUbot : U = ⊥ := Subgroup.eq_bot_of_card_eq U hU1
  have hab : ∀ x y : S, x * y = y * x := by
    intro x y
    have hx : x ∈ T := by rw [hTtop]; trivial
    have hy : y ∈ T := by rw [hTtop]; trivial
    have h2 := hcomm x hx y hy
    rw [hUbot, Subgroup.mem_bot, commutatorElement_def] at h2
    have h3 : x * y * x⁻¹ = y := mul_inv_eq_one.mp h2
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h3]
  have hAtop : A = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact h.A_cent x (fun a _ => hab x a)
  have h8 := h.A_card
  rw [hAtop, Subgroup.card_top] at h8
  omega

theorem noE32_of_caseIc [Finite S] (hS : IsPGroup 2 S) {A E : Subgroup S} (h : Cfg S A E)
    (hcard : Nat.card ↥(A ⊓ E) = 4)
    (hN : Nat.card ↥(Subgroup.normalizer (A : Set S)) ≤ 32) : NoE32 S := by
  by_cases hsmall : Nat.card S ≤ 32
  · exact noE32_of_small h hsmall
  · push Not at hsmall
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    have h64 : 64 ≤ Nat.card S := by
      by_contra hlt
      push Not at hlt
      have hn6 : n ≤ 5 := by
        by_contra hn6
        push Not at hn6
        have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn6
        omega
      have : 2 ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hn6
      omega
    have hAE : ∃ a ∈ A, a ∉ E := by
      by_contra hno
      push Not at hno
      have : A ⊓ E = A := inf_eq_left.mpr hno
      rw [this, h.A_card] at hcard
      omega
    obtain ⟨a, ha, haE⟩ := hAE
    have ha2 : a * a ∈ E := by rw [h.A_sq a ha]; exact E.one_mem
    have hsuz : HasSuz S E :=
      hasSuz_of_centralizer hS (E := E) h.E_norm haE ha2
        (D := Subgroup.normalizer (A : Set S))
        (fun x hx => h.caseI_mem_normalizer hcard ha haE hx)
        (by rw [h.E_card]; exact hN) (by rw [h.E_card]; omega)
    exact noE32_of_caseIc_aux hS h hcard hsuz

theorem noE32_of_cfg [Finite S] (hS : IsPGroup 2 S) {A E : Subgroup S} (h : Cfg S A E) :
    NoE32 S := by
  obtain ⟨z, hzE, hz1, hzc⟩ := h.exists_z hS
  have hzA : z ∈ A := h.A_cent z (fun a _ => (hzc a).symm)
  have hdvd : Nat.card ↥(A ⊓ E) ∣ 8 := by
    rw [← h.A_card]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hge : 2 ≤ Nat.card ↥(A ⊓ E) := by
    classical
    have h3 := finset_card_le_subgroup ({1, z} : Finset S) (A ⊓ E) (by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact (A ⊓ E).one_mem
      · exact ⟨hzA, hzE⟩)
    have h4 : ({1, z} : Finset S).card = 2 := Finset.card_pair (Ne.symm hz1)
    omega
  have hcases : Nat.card ↥(A ⊓ E) = 2 ∨ Nat.card ↥(A ⊓ E) = 4 ∨ Nat.card ↥(A ⊓ E) = 8 := by
    have hle : Nat.card ↥(A ⊓ E) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card ↥(A ⊓ E) <;> omega
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := h.A_comm
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => by rw [pow_two]; exact h.A_sq a ha
  rcases hcases with h2 | h4 | h8
  · exact noE32_of_caseII hS h h2
  · by_cases hNtop : Subgroup.normalizer (A : Set S) = ⊤
    · exact noE32_of_normal hS hAcomm hA2 h.A_card h.centralizer_eq
        (Subgroup.normalizer_eq_top_iff.mp hNtop)
    · have hle := h.card_normalizer_le hS
      obtain ⟨k, hk⟩ := (hS.to_subgroup (Subgroup.normalizer (A : Set S))).exists_card_eq
      by_cases h32 : Nat.card ↥(Subgroup.normalizer (A : Set S)) ≤ 32
      · exact noE32_of_caseIc hS h h4 h32
      · push Not at h32
        have h64 : Nat.card ↥(Subgroup.normalizer (A : Set S)) = 64 := by
          have hk6 : k ≤ 6 := by
            by_contra hk6
            push Not at hk6
            have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk6
            omega
          have hk5 : 5 < k := by
            by_contra hk5
            push Not at hk5
            have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hk5
            omega
          have : k = 6 := by omega
          rw [hk, this]
          norm_num
        exact noE32_of_caseIa hS h h4 h64 hNtop
  · have hAE : A ⊓ E = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, h.A_card])
    have hAle : A ≤ E := by
      intro x hx
      have : x ∈ A ⊓ E := by rw [hAE]; exact hx
      exact this.2
    have hAEeq : A = E := Subgroup.eq_of_le_of_card_ge hAle (by rw [h.A_card, h.E_card])
    have hAn : A.Normal := by rw [hAEeq]; exact h.E_normal
    exact noE32_of_normal hS hAcomm hA2 h.A_card h.centralizer_eq hAn

end CFSG.OddStandard.Harada75

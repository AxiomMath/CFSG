module

public import CFSG.LocalAnalysis.OddStandard.Harada75Rank
public import CFSG.LocalAnalysis.OddStandard.Harada75Aut
public import CFSG.LocalAnalysis.OddStandard.Harada75Count

public section

namespace CFSG.OddStandard.Harada75

open Subgroup
open scoped commutatorElement

variable {S : Type} [Group S]

theorem eq_one_or_eq_of_card_two [Finite S] {U : Subgroup S} (hU : Nat.card U = 2) {u : S}
    (hu : u ∈ U) (hu1 : u ≠ 1) : ∀ x ∈ U, x = 1 ∨ x = u := by
  classical
  intro x hx
  by_contra hne
  push Not at hne
  have h3 := finset_card_le_subgroup ({1, u, x} : Finset S) U (by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact U.one_mem
    · exact hu
    · exact hx)
  have h4 : ({1, u, x} : Finset S).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, u, x, hu1.symm, hne.1.symm, hne.2.symm, rfl⟩
  omega

theorem noE32_of_normal [Finite S] (hS : IsPGroup 2 S) {A : Subgroup S}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hA8 : Nat.card A = 8) (hCA : Subgroup.centralizer (A : Set S) = A) (hAn : A.Normal) :
    NoE32 S := by
  intro T U ⟨hUT, hsq, hcomm, hcard⟩
  have hX : ∀ x ∈ T, ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun x _ a ha => hAn.conj_mem a ha x
  have hT2 : IsPGroup 2 T := hS.to_subgroup T
  have h1 := card_le_eight_mul_card_inf_centralizer hAc hA2 hA8 hT2 hX
  rw [hCA] at h1
  have hMA : Nat.card ↥(T ⊓ A) ≤ 8 := by
    have := Subgroup.card_le_of_le (inf_le_right : T ⊓ A ≤ A)
    rwa [hA8] at this
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hU12 : Nat.card U = 1 ∨ Nat.card U = 2 := by omega
  have hMeq : Nat.card ↥(T ⊓ A) = 8 → A ≤ T := by
    intro h
    have hle : T ⊓ A ≤ A := inf_le_right
    have heq : T ⊓ A = A := Subgroup.eq_of_le_of_card_ge hle (by rw [h, hA8])
    intro x hx
    have : x ∈ T ⊓ A := by rw [heq]; exact hx
    exact this.1
  rcases hU12 with hU | hU
  ·
    have hUb : U = ⊥ := Subgroup.eq_bot_of_card_eq U hU
    have hab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
      intro x hx y hy
      have h2 := hcomm x hx y hy
      rw [hUb, Subgroup.mem_bot, commutatorElement_def] at h2
      have h3 : x * y * x⁻¹ = y := mul_inv_eq_one.mp h2
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [h3]
    have hT32 : Nat.card T = 32 := by omega
    have hM4 : 4 ≤ Nat.card ↥(T ⊓ A) := by omega
    by_cases hM8 : Nat.card ↥(T ⊓ A) = 8
    · have hAT := hMeq hM8
      have hTA : T ≤ A := by
        intro t ht
        rw [← hCA, Subgroup.mem_centralizer_iff]
        intro a ha
        exact (hab t ht a (hAT ha)).symm
      have := Subgroup.card_le_of_le hTA
      omega
    · have hM4' : Nat.card ↥(T ⊓ A) = 4 := by
        obtain ⟨k, hk⟩ := (hS.to_subgroup (T ⊓ A)).exists_card_eq
        have hk3 : k ≤ 3 := by
          by_contra hlt
          push Not at hlt
          have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
          omega
        have hk' : Nat.card ↥(T ⊓ A) = 2 ^ k := hk
        interval_cases k <;> omega
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_commutator_not_mem_centralizer hAc hA2 hA8 hT2 hX
        (by rw [hCA]; omega)
      apply hxy
      rw [hCA]
      have : x * y = y * x := hab x hx y hy
      have h5 : ⁅x, y⁆ = 1 := by
        rw [commutatorElement_def, this]; group
      rw [h5]
      exact A.one_mem
  ·
    have hM8 : Nat.card ↥(T ⊓ A) = 8 := by omega
    have hAT := hMeq hM8
    have hT64 : Nat.card T = 64 := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_commutator_not_mem_centralizer hAc hA2 hA8 hT2 hX
      (by rw [hCA]; omega)
    apply hxy
    rw [hCA]
    have hxyU := hcomm x hx y hy
    by_cases hU1 : ∀ u ∈ U, u = 1
    · rw [hU1 _ hxyU]; exact A.one_mem
    · push Not at hU1
      obtain ⟨u, huU, hu1⟩ := hU1
      have hstruct := eq_one_or_eq_of_card_two hU huU hu1
      have hUA : ∀ v ∈ U, v ∈ A := by
        intro v hv
        rw [← hCA, Subgroup.mem_centralizer_iff]
        intro a ha
        have haT : a ∈ T := hAT ha
        have hvT : v ∈ T := hUT hv
        have h1' : a * v * a⁻¹ ∈ U := by
          have := U.mul_mem (hcomm a haT v hvT) hv
          rw [commutatorElement_def] at this
          have e : a * v * a⁻¹ * v⁻¹ * v = a * v * a⁻¹ := by group
          rwa [e] at this
        rcases hstruct v hv with rfl | rfl
        · simp
        · rcases hstruct _ h1' with h2 | h2
          · exfalso
            have : v = 1 := by
              calc v = a⁻¹ * (a * v * a⁻¹) * a := by group
                _ = 1 := by rw [h2]; group
            exact hu1 this
          · calc a * v = a * v * a⁻¹ * a := by group
              _ = v * a := by rw [h2]
      exact hUA _ hxyU

end CFSG.OddStandard.Harada75

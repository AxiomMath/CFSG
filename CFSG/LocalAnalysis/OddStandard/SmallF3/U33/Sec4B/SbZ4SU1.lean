module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Syl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem z4_not_isSylowIn_of_normalizes {U N : Subgroup G} (hU : IsPGroup 2 U)
    (hN : ∀ n : G, (∀ x ∈ U, n * x * n⁻¹ ∈ U) → n ∈ N)
    (hcard : Nat.card U < 2 ^ 11) (hdvd : 2 ^ 11 ∣ Nat.card G) : ¬ IsSylowIn 2 U N := by
  intro hS
  obtain ⟨𝒮, h𝒮, hU𝒮⟩ := S4B.exists_isSylowIn_of_le (K := ⊤) le_top hU
  have hrel : 𝒮.relIndex ⊤ * Nat.card 𝒮 = Nat.card G := by
    have h := Subgroup.relIndex_mul_card (H := 𝒮) (K := ⊤)
    rwa [inf_top_eq, Subgroup.card_top] at h
  have hcop : Nat.Coprime (2 ^ 11) (𝒮.relIndex ⊤) :=
    (Nat.coprime_pow_left_iff (by norm_num) 2 _).mpr
      ((Nat.prime_two.coprime_iff_not_dvd).mpr h𝒮.2.2)
  have hdvdS : 2 ^ 11 ∣ Nat.card 𝒮 := by
    rw [← hrel] at hdvd
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hleS : 2 ^ 11 ≤ Nat.card 𝒮 := Nat.le_of_dvd Nat.card_pos hdvdS
  have hex : ∃ n ∈ 𝒮, (∀ x ∈ U, n * x * n⁻¹ ∈ U) ∧ n ∉ U := by
    by_contra h
    have hforall : ∀ n ∈ 𝒮, (∀ x ∈ U, n * x * n⁻¹ ∈ U) → n ∈ U := by
      intro n hn hnorm
      by_contra hnU
      exact h ⟨n, hn, hnorm, hnU⟩
    have hUS : U = 𝒮 := S4B.eq_of_forall_normalizes h𝒮.2.1 hU𝒮 hforall
    have hcardUS : Nat.card U = Nat.card 𝒮 := by rw [hUS]
    omega
  obtain ⟨n, hn𝒮, hnorm, hnU⟩ := hex
  have hnN : n ∈ N := hN n hnorm
  let D : Subgroup G := U ⊔ zpowers n
  have hDN : D ≤ N := sup_le hS.1 (Subgroup.zpowers_le.mpr hnN)
  have hD𝒮 : D ≤ 𝒮 := sup_le hU𝒮 (Subgroup.zpowers_le.mpr hn𝒮)
  have hD2 : IsPGroup 2 D := h𝒮.2.1.to_le hD𝒮
  have hcardD : Nat.card U ≤ Nat.card D := Subgroup.card_le_of_le le_sup_left
  obtain ⟨c, _hcN, hcj⟩ := S4B.exists_cj_of_card_le hS hDN hD2 hcardD
  have hcardEq : Nat.card D = Nat.card U := by rw [← hcj, S4B.card_cj]
  have hUD : U = D := Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq hcardEq)
  have hnD : n ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  exact hnU (hUD.symm ▸ hnD)

end CFSG.OddStandard.SmallF3.HarrisU33

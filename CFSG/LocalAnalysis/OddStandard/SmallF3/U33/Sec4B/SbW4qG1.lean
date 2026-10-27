module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Syl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem w4q_mem_of_normalizes {P K : Subgroup G} (hP : IsSylowIn 2 P K) {c : G} (hcK : c ∈ K)
    (hcN : ∀ s ∈ P, c * s * c⁻¹ ∈ P) (hc2 : c ^ 2 ∈ P) : c ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : zpowers c ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype (S := (P : Set G)) hcN)
  have hzp2 : IsPGroup 2 (zpowers c) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := ↥P)).mp hP.2.1
    refine IsPGroup.of_card_dvd_pow (n := m + 1) ?_
    rw [Nat.card_zpowers]
    have h1 : orderOf c ∣ 2 * orderOf (c ^ 2) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, pow_orderOf_eq_one]
    have h2 : orderOf (c ^ 2) ∣ 2 ^ m := by
      have hdvd : Nat.card (zpowers (c ^ 2)) ∣ Nat.card P :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hc2)
      rwa [Nat.card_zpowers, hm] at hdvd
    have h3 : 2 * orderOf (c ^ 2) ∣ 2 ^ (m + 1) := by
      rw [pow_succ' 2 m]
      exact Nat.mul_dvd_mul_left 2 h2
    exact dvd_trans h1 h3
  let D : Subgroup G := P ⊔ zpowers c
  have hD2 : IsPGroup 2 D := IsPGroup.to_sup_of_normal_left' hP.2.1 hzp2 hnorm
  have hDK : D ≤ K := sup_le hP.1 (Subgroup.zpowers_le.mpr hcK)
  have hcard : Nat.card P ≤ Nat.card D := Subgroup.card_le_of_le le_sup_left
  obtain ⟨c', _hc'K, hcj⟩ := exists_cj_of_card_le hP hDK hD2 hcard
  have hcardD : Nat.card D = Nat.card P := by rw [← hcj, card_cj]
  have hPD : P = D := Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq hcardD)
  rw [hPD]
  change c ∈ P ⊔ zpowers c
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

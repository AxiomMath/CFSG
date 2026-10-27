module

public import CFSG.GH74.Generic.S45.L1310
public import CFSG.GH74.Generic.S45.LAltL2
public import CFSG.GH74.Generic.S45.LAltLift

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup

theorem Hyp1310.data {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (h : Hyp1310 K y L) :
    Group.IsPerfect K ∧ IsPGroup 2 (Subgroup.center K) ∧ orderOf y = 2 ∧
      (∀ l ∈ L, y l = l) ∧ (∀ m : K, y m = m → ¬ 4 ∣ orderOf m) ∧ IsSimpleGroup ↥L ∧
      (∃ a b : ↥L, a * b ≠ b * a) ∧ (∃ v ∈ L, orderOf v = 2) ∧
      ∃ q : ℕ, 5 ≤ q ∧ Odd q ∧ Nat.card ↥L * 2 = q * (q ^ 2 - 1) ∧
        ∀ P : ℕ → Prop, P q → HasL2Model ↥L P := by
  obtain ⟨hK, hy, hL, -, hL2, hA, -, -⟩ := h
  have hz2 : IsPGroup 2 (Subgroup.center K) := by
    rw [hK.2.1]
    exact CFSG.pCore_isPGroup
  obtain ⟨hLs, hLnab, ⟨v, hv⟩, q, hq5, hqodd, hqcard, hmodel⟩ := LAlt.hasL2Model_data hL2
  refine ⟨hK.1.1, hz2, hy, fun l hl => hL hl y (Subgroup.mem_zpowers y), fun m hm =>
    LAlt.not_four_dvd_orderOf (M := fixSub (zpowers y)) hA (fix_mem_zpowers hm), hLs, hLnab,
    ⟨(v : K), v.2, by rw [Subgroup.orderOf_coe]; exact hv⟩, q, hq5, hqodd, hqcard, hmodel⟩

theorem eq_five_of_card_dvd_120 {N q : ℕ} (hN : N ∣ 120) (hq5 : 5 ≤ q) (hqodd : Odd q)
    (h : N * 2 = q * (q ^ 2 - 1)) : q = 5 := by
  have hN120 : N ≤ 120 := Nat.le_of_dvd (by norm_num) hN
  have hq6 : q ≤ 6 := by
    by_contra hgt
    push Not at hgt
    have h1 : 7 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 7 * (7 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right h1 1)
    omega
  obtain ⟨k, hk⟩ := hqodd
  omega

end CFSG.GH74.Generic.S45

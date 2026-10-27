module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CentralOdd
public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.RankThree.OddKernel.SporadicKernelRestrictionB

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.GMS
  CFSG.Blueprint.NativeSporadic

theorem three_pow_le_of_babyInv {k : Fin 4} {j : ℕ} (h : 3 ^ j ∣ babyCentOrder k) : j ≤ 9 := by
  by_contra hj
  have h10 : 3 ^ 10 ∣ babyCentOrder k :=
    (pow_dvd_pow 3 (by omega : 10 ≤ j)).trans h
  fin_cases k <;> simp [babyCentOrder] at h10

section ThreeCentral


theorem odd_card_gLAPPrimeCoreOf_B_of_three_central {s : B}
    (h13 : 3 ^ 13 ∣ Nat.card (Subgroup.centralizer ({s} : Set B))) :
    Odd (Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set B)))) := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({s} : Set B) with hC
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 3 h13
  set P : Subgroup B := K.map C.subtype with hP
  have hPcard : Nat.card P = 3 ^ 13 := by
    rw [hP, Subgroup.card_map_of_injective C.subtype_injective, hK]
  have hPp : IsPGroup 3 P := IsPGroup.of_card hPcard
  have hPC : P ≤ C := Subgroup.map_subtype_le K
  refine odd_card_gLAPPrimeCoreOf_of_large_pGroup Nat.prime_three hPC hPp
    (k := 4) hPcard ?_ ?_
  · intro w hw hw1 R hRp hRw
    have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw) hw1
    obtain ⟨k, hk⟩ := (CFSG.Monster.Existence.babyTableIII.1 w hwo)
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hRp
    have hdvd : 3 ^ j ∣ babyCentOrder k := by
      rw [← hj, ← hk.2]
      exact Subgroup.card_dvd_of_le hRw
    have hj9 := three_pow_le_of_babyInv hdvd
    rw [hj]
    calc 3 ^ j * 3 ^ 4 ≤ 3 ^ 9 * 3 ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hj9)
      _ = 3 ^ 13 := by norm_num
  · intro m hm hmod
    rw [CFSG.RankThree.OddKernel.card_B_eq] at hm
    have hm41 : m ≤ 41 := by
      by_contra hlt
      have : 2 ^ 42 ∣ 4154781481226426191177580544000000 :=
        (pow_dvd_pow 2 (by omega : 42 ≤ m)).trans hm
      exact absurd this (by decide)
    have hcheck : ∀ m' < 42, 2 ^ m' % 81 = 1 → m' = 0 := by decide
    exact hcheck m (by omega) hmod

end ThreeCentral

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance

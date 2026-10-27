module

import CFSG.Quasithin.Background.F420Orders
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A312Sub

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X7a

theorem card_psl_two_even {X : Type} [Group X] {n : ℕ} (h : StatedClassicalModel X .PSL 2 2 n) :
    Nat.card X = 2 ^ n * (4 ^ n - 1) :=
  CFSG.Quasithin.F420.card_of_statedPSL_two_two h

section Three

variable {K : Type} [Field K] [Finite K]

theorem card_projectiveSL_three_mul :
    Nat.card (projectiveSL 3 K) * Nat.card (scalars 3 K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  have h1 := (scalars 3 K).card_eq_card_quotient_mul_card_subgroup
  have h2 := card_SL_eq (K := K) (n := 3) (by norm_num)
  have hI : ∏ j ∈ Finset.Icc 2 3, (Nat.card K ^ j - 1) = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  rw [hI] at h2
  have h3 : Nat.card (projectiveSL 3 K) = Nat.card (Matrix.SpecialLinearGroup (Fin 3) K ⧸ scalars 3 K) :=
    rfl
  rw [h3, ← h1, h2]

omit [Finite K] in
theorem card_scalars_three_le : Nat.card (scalars 3 K) ≤ 3 := by
  rw [scalars_eq_center, Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, by norm_num⟩ : Fin 3)).toEquiv]
  simpa using card_rootsOfUnity K 3

omit [Finite K] in
theorem pow_three_sub_one_dvd_seven (m : ℕ) : 7 ∣ (2 ^ m) ^ 3 - 1 := by
  have := Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (m := 3) (k := 3 * m) (Dvd.intro m rfl)
  have h8 : (2 ^ m) ^ 3 = 2 ^ (3 * m) := by rw [← pow_mul, mul_comm]
  rw [h8]
  simpa using this

end Three

section Orders

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem seven_dvd_card_psl_three_even {X : Type} [Group X] {m : ℕ}
    (h : StatedClassicalModel X .PSL 3 2 m) : 7 ∣ Nat.card X := by
  obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr (e.trans (statedSLEquivProjectiveSL 3 K)).toEquiv]
  have hmul := card_projectiveSL_three_mul (K := K)
  rw [hK] at hmul
  have h7 : 7 ∣ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (pow_three_sub_one_dvd_seven m) _) _
  rw [← hmul] at h7
  have hle := card_scalars_three_le (K := K)
  have hpos : 0 < Nat.card (scalars 3 K) := Nat.card_pos
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7 with h | h
  · exact h
  · exfalso
    have := Nat.le_of_dvd hpos h
    omega

theorem card_psl_three_four {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 2 2) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem card_psl_three_three {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 3 1) :
    Nat.card X = 5616 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three h

theorem thirtytwo_dvd_card_psp_four_even {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (h : StatedClassicalModel X .PSp 2 2 m) : 32 ∣ Nat.card X := by
  obtain ⟨⟨-, hm1, -⟩, K, hF, hFin, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hm1 hK
  rw [Nat.card_congr e.toEquiv]
  have hbij : Function.Bijective (SymplecticFlag.proj 2 K) :=
    ⟨proj_injective_charTwo, SymplecticHigher.proj_surjective⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), card_statedSp 2, hK]
  have h1 : ∏ j ∈ Finset.Icc 1 2, ((2 ^ m) ^ (2 * j) - 1) = ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  rw [h1]
  refine Dvd.dvd.mul_right ?_ _
  have : 2 ^ 5 ∣ (2 ^ m) ^ 2 ^ 2 := by
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by norm_num; omega)
  simpa using this

end Orders

end A312Sub

end CFSG.QuasithinUnique.Unc25G2
